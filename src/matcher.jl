#ldoc on
##
# ## A matching example
#
# Beyond writing language utilities, Julia macros are useful for writing
# embedded domain-specific languages (DSLs) for accomplishing particular
# tasks.  In this setting, we are really writing a language interpreter
# embedded in Julia, using the Julia parse tree as an input and
# producing Julia code as output.
#
# As an example of both Julia macro design and Julia programming more
# generally, we will design a small language extension for writing
# functions that transform code based on structural pattern matching;
# for example, a rule written as:
# ```{.julia}
# 0-x => x -> -x
# ```
# corresponds to a function something like
# ```{.julia}
# e ->
#     # Check that e is a binary minus and the first argument is zero.
#     if (e isa Expr && e.head == :call &&
#         e.args[1] == :- && length(e.args) == 3 &&
#         e.args[2] == 0)
#
#         # Bind the name "x" to the second argument
#         let x = e.args[3]
#             result = :(-$x)   # Create a "-x" expression
#             true, result      # Yes it matched, return result
#         end
#     else
#         false, nothing        # No, it didn't match
#     end
# ```
# That is, we want a function that takes an input
#
# - Is this an expression with a binary `-` operation at the top?
# - Is the second term in the sum a zero?
# - If both are true, bind `x` to the second term in the sum,
#   produce a new expression `:(-$x)`, and assign to `result`.
#   Return the pair `(true, result)`.
# - Otherwise, return `(false, nothing)`.
#
# The one-line description is already more concise for this simple
# example; if we wanted to match against a more complicated pattern,
# the Julia code corresponding to a rule in the syntax
# ```{.julia}
# pattern => (argument_symbols) -> result_code
# ```
# becomes that much more complex.  Our key task is therefore take rules
# written with the first syntax and to convert them automatically to
# standard functions.
#
# This is a more ambitious example, and can be
# safely skipped over.  However, it is both a useful example of a
# variety of features in Julia and introduces concrete tools we will use
# in later chapters (e.g. when discussing automatic differentiation).
#
# ### Preprocessing
#
# The parse tree for Julia code includes not only expressions, but also
# *line numbers*, e.g.
# ```{julia}
# :(x->x+1)
# ```
# In the code shown, the comment line immediately after the `begin`
# statement corresponds to a `LineNumberNode`.  Such `LineNumberNode`
# nodes are useful for debugging, but are a nuisance for our attempts at
# pattern matching.  Therefore, before doing anything else, we will
# write a utility to get rid of such nodes.  Because `LineNumberNode` is
# a distinct type, we can use Julia's multiple dispatch as an easy way
# to accomplish this.

filter_line_numbers(e :: Expr) =
    let args = filter(a -> !(a isa LineNumberNode), e.args)
        Expr(e.head, filter_line_numbers.(args)...)
    end
filter_line_numbers(e) = e

##
# ### Matching
#
# At the heart of our matching algorithm will be a function `match_gen`
# that generates code to check whether an expression matches a pattern.
# The inputs to the `match_gen` function are
#
# - A dictionary of *bindings*, mapping symbols to values.
# - A pattern
# - A symbol naming the current expression being matched.
#
# #### Literals
#
# In the simplest case, for non-symbol leaf nodes, we declare a match
# when the pattern agrees with the expression.

match_gen!(bindings, e, pattern) = :($e == $pattern)

##
# For example, the following code matches the expression named `expr` to
# the pattern `0`:
# ```{julia}
# match_gen!(Dict(), :expr, 0)
# ```
#
# #### Symbols
#
# Things are more complicated when we match a symbol.  If the symbol is
# not in the bindings dictionary, we just check that the expression
# equals the (quoted) symbol.  Otherwise, there are two cases:
#
# - *First use*: we create a new binding for it.
# - *Repeat use*: Check if `expr` matches the previous binding.

match_gen!(bindings, e, s :: Symbol) =
    if !(s in keys(bindings))
        qs = QuoteNode(s)
        :($e == $qs)
    elseif bindings[s] == nothing
        binding = gensym()
        bindings[s] = binding
        quote $binding = $e; true end
    else
        binding = bindings[s]
        :($e == $binding)
    end

##
# We illustrate all three cases below.
# ```{julia}
# let
#     bindings = Dict{Symbol,Any}(:x => nothing)
#     println( match_gen!(bindings, :expr, :x) )
#     println( match_gen!(bindings, :expr, :x) )
#     println( match_gen!(bindings, :expr, :y) )
# end
# ```
#
# #### Expressions
# 
# The most complex case is matching expressions.  The basics are not
# complicated: an item `e` matches an `Expr` pattern if `e` is an
# expression with the same head as the pattern and if the arguments match.

match_gen!(bindings, e, pattern :: Expr) =
    let head = QuoteNode(pattern.head),
        argmatch = match_gen_args!(bindings, e, pattern.args)
        :( $e isa Expr && $e.head == $head && $argmatch )
    end

##
# The building block for checking the arguments will be to check that a
# list of expressions matches a list of patterns.

match_gen_lists!(bindings, exprs, patterns) =
    foldr((x,y) -> :($x && $y),
          [match_gen!(bindings, e, p)
           for (e,p) in zip(exprs, patterns)])

##
# The more complicated case is ensuring that the arguments match.
# This is in part because we want to accomodate the possibility that the
# last argument in the list is "splatted"; that is, a pattern like
# `f(args...)` should match `f(1, 2, 3)` with `args` bound to the tuple
# `[1, 2, 3]`.  In order to do this, we would first like to make sure
# that we can sensibly identify a "splatted argument."

is_splat_arg(bindings, e) =
    e isa Expr &&
    e.head == :(...) &&
    e.args[1] isa Symbol &&
    e.args[1] in keys(bindings)

##
# Note that we only consider something a "splatted argument" if the
# argument to the splat operator is a symbol in the bindings table.
#
# To implement the check, we create a `let` statement to bind a local
# name to each argument.  If the last pattern is splatted, we make sure
# the last term in the tuple on the left-hand side of the statement is
# splatted (and then remove the pattern splat).  Finally, we generate
# checks to make sure each of the locally-named arguments matches with
# the associated term in the pattern list.

match_gen_args!(bindings, e, patterns) =
    if isempty(patterns)
        :(length($e.args) == 0)
    else
        nargs = length(patterns)
        lencheck = :(length($e.args) == $nargs)
        args = Vector{Any}([gensym() for j = 1:length(patterns)])
        argstuple = Expr(:tuple, args...)

        # De-splat pattern / splat arg assignment and
        #   adjust the length check
        if is_splat_arg(bindings, patterns[end])
            patterns = copy(patterns)
            patterns[end] = patterns[end].args[1]
            argstuple.args[end] = Expr(:(...), argstuple.args[end])
            lencheck = :(length($e.args) >= $(nargs-1))
        end

        argchecks = match_gen_lists!(bindings, args, patterns)
        :($lencheck && let $argstuple = $e.args; $argchecks end)
    end

##
# We strongly recommend the reader trace through this code for some
# examples until enlightenment strikes.
#
# #### Compiling the match
# 
# Given a list of symbols and a pattern in which they appear, we can
# produce code to generate a mapping from expressions to either
# `(true,bindings)` where `bindings` is a list of all the subexpressions
# bound to the name list; or `(false, nothing)` if there is no match.

function compile_matcher(symbols, pattern)
    bindings = Dict{Symbol,Any}(s => nothing for s in symbols)

    # Input expression symbol and matching code
    # (symbol bindings are indicated by bindings table)
    expr = gensym()
    test = match_gen!(bindings, expr, pattern)

    # Get result vals (symbol/nothing) and associated variable names
    result_vals = [bindings[s] for s in symbols]
    declarations = filter(x -> x != nothing, result_vals)

    # Produce the matching code
    results = Expr(:tuple, result_vals...)
    :($expr ->
        let $(declarations...)
            if $test
                (true, $results)
            else
                (false, nothing)
            end
        end)
end

##
# It is convenient to compile this into a macro.  The macro version also
# filters line numbers out of the input pattern and out of any exprssion
# we are trying to match.

macro match(symbols, pattern)
    @assert(symbols.head == :tuple &&
            all(isa.(symbols.args, Symbol)),
            "Invalid input symbol list")

    pattern = filter_line_numbers(pattern)
    matcher = compile_matcher(symbols.args, pattern)
    esc(:($matcher ∘ filter_line_numbers))
end

##
# ### Rules
# 
# A rule has the form
# ```{.julia}
# pattern => args -> code
# ```
# where `args` is the list of names that are bound in the pattern, and
# these names can be used in the subsequent code.  We want to allow the
# code to potentially use not only the matched subexpression, but also
# to refer to the symbol as a whole; we use the named argument feature
# in tuples for that.  So, for example, in the rule
# ```{.julia}
# x - y => (x,y;e) -> process(e)
# ```
# we mean to match any subtraction, bind the operands to `x` and `y` and the
# expression as a whole to `e`, and call `process(e)` to process the expression.
# 
# Now that we have a macro for computing matches, we can use it to
# help with parsing the rule declarations into argument names,
# expression name (if present), the pattern, and the code to be called
# on a match.

function parse_rule(rule)
    match_rule = @match (pattern, args, code) pattern => args -> code
    isok, rule_parts = match_rule(rule)
    if !isok
        error("Syntax error in rule $rule")
    end
    pattern, args, code = rule_parts

    match_arg1 = @match (args, expr) (args..., ; expr)
    match_arg2 = @match (args, expr) (args..., )
    begin ismatch, bindings = match_arg1(args); ismatch end ||
    begin ismatch, bindings = match_arg2(args); ismatch end ||
    begin bindings = (Vector{Any}([args]), nothing) end
    symbols, expr_name = bindings

    if !all(isa.(symbols, Symbol))
        error("Arguments should all be symbols in $symbols")
    end
    if !(expr_name == nothing || expr_name isa Symbol)
        error("Expression parameter should be a symbol")
    end

    symbols, expr_name, pattern, code
end

##
# Matching a pattern on an input produces a boolean variable (whether
# there was a match or not) and a table of bindings from names in the
# pattern to symbols generated during the match.  In order to safely
# access the right-hand-side symbols that were generated during the
# match, we need to declare them (in a `let` statement).  If there is a
# match, we bind them to the ordinary input names (things like `:x`) in
# a second let statement, then call the code in that second let
# statement and assign the result to the `result` symbol.
# The resulting code must be used in a context where the `expr`
# and `result` symbols are already set up.

function compile_rule(rule, expr, result)

    symbols, expr_name, pattern, code = parse_rule(rule)
    bindings = Dict{Symbol,Any}(s => nothing for s in symbols)
    test = match_gen!(bindings, expr, pattern)

    # Get list of match symbols and associated declarations
    result_vals = [bindings[s] for s in symbols]
    declarations = filter(x -> x != nothing, result_vals)

    # Set up local bindings of argument names in code
    binding_code = [:($s = $(r == nothing ? (:nothing) : r))
                    for (s,r) in zip(symbols, result_vals)]
    if expr_name != nothing
        push!(binding_code, :($expr_name = $expr))
    end

    # Produce the rule
    ismatch = gensym()
    quote
        let $(declarations...)
            $ismatch = $test
            if $ismatch
                $result = let $(binding_code...); $code end
            end
            $ismatch
        end
    end
end

##
# Now that we are able to compile a rule, we set up a macro for
# compiling a rule into a standalone function.  The input expression
# symbol (`expr`) is the named argument to this standalone function,
# and at the end the function returns both the match condition
# (which is what the compiled code evaluates to) and the result
# (which the compiled code produces as a side effect).

macro rule(r)
    expr, result = gensym(), gensym()
    code = compile_rule(filter_line_numbers(r), expr, result)
    esc(quote
            $expr ->
                let $result = nothing
                    $code, $result
                end
        end)
end

##
# Finally, we often want to combine rules, executing the first one that
# matches a given input.  The `@rules` macro takes a set of rules
# packaged into a block and tries them in sequence, returning the result
# of whichever rule was executed (or `nothing` if no rule was executed).

macro rules(rblock :: Expr)
    rblock = filter_line_numbers(rblock)
    if rblock.head != :block
        error("Rules must be in a begin/end block")
    end

    # Set up input name, output name, and rule list
    expr, result = gensym(), gensym()
    rules = rblock.args

    # Or together all the tests
    rule_calls =
        foldr((x,y) -> :($x || $y),
              [compile_rule(r, expr, result) for r in rules])

    # Call all the rules, return the computed result
    esc(quote
            $expr ->
                let $result = nothing
                    $rule_calls
                    $result
                end
        end)
end

##
# ### Examples
# 
# We conclude our matching example by giving a few examples of the
# process in practice.
# 
# #### Re-associating operations
# 
# Julia parses chains of additions and multiplications into one long
# list.  For example, `1+2+3` parses to `(1+2)+3` rather than
# to `+(+(1,2), 3)`.  For some operations, it is simpler to only allow
# binary addition and multiplication nodes.  The following function
# converts these nodes.

function reassoc_addmul(e)

    # Apply folding to an op(args...) node (op = +, *)
    fold_args(args, op) =
        foldl((x,y) -> :($op($x, $y)), args)

    # Rules for processing one expression node
    r = @rules begin
        +(args...) => args -> fold_args(args, :+)
        *(args...) => args -> fold_args(args, :*)
        e => e -> e
    end

    # Recursively process the graph
    process(e :: Expr) = r(Expr(e.head, process.(e.args)...))
    process(e) = e

    # Process the input expression
    process(e)
end

##
# For example, the following expression has both long sums and
# long products that we re-associate into binary operations.
# 
# ```{julia}
# let
#     e = :(sin(1+2+3*4*f))
#     println("Original:    $e")
#     println("Transformed: $(reassoc_addmul(e))")
# end
# ```
# 
# If we wanted to, we could also "de-associate" by collapsing sums and
# multiplications into single nodes.

function deassociate(e)
    r = @rules begin
        x * (*(args...)) => (x, args) -> Expr(:call, :*, x, args...)
        (*(args...)) * x => (args, x) -> Expr(:call, :*, args..., x)
        x + (+(args...)) => (x, args) -> Expr(:call, :+, x, args...)
        (+(args...)) + x => (args, x) -> Expr(:call, :+, args..., x)
        e => e -> e
    end
    process(e :: Expr) = r(Expr(e.head, process.(e.args)...))
    process(e) = e
    process(e)
end

##
# We take the output of our "reassociate" code as an example input.
# ```{julia}
# deassociate(:(sin((1+2) + (3*4)*f)))
# ```
# 
# #### Simplifying expressions
# 
# Automatically-generated code of the sort that comes out of naive
# automatic differentiation often involves operations that can be
# easily simplified by removing additions with zeros, multiplications
# with one, and so forth.  For example, we write `simplify_sum` and
# `simplify_mul` routines to handle simplification of sums and products
# involving zeros and ones.

simplify_sum(args) =
    let args = filter(x -> x != 0, args)
        if length(args) == 1
            args[1]
        else
            Expr(:call, :+, args...)
        end
    end

simplify_mul(args) =
    let args = filter(x -> x != 1, args)
        if any(args .== 0)
            0
        elseif length(args) == 1
            args[1]
        else
            Expr(:call, :*, args...)
        end
    end

##
# Building on simplifying sums and products, we can recurse up and down
# an expression tree to apply these and other similar rules.

function simplify(e)
    r = @rules begin
        +(args...) => args -> simplify_sum(args)
        *(args...) => args -> simplify_mul(args)
        x - 0 => x -> x
        0 - x => x -> :(-$x)
        -(0)  => (;x) -> 0
        x / 1 => x -> x
        0 / x => x -> 0
        x ^ 1 => x -> x
        x ^ 0 => x -> 1
        e     => e -> e
    end
    process(e :: Expr) = r(Expr(e.head, process.(e.args)...))
    process(e) = e
    process(e)
end

##
# We illustrate our simplifier with some operations
# ```{julia}
# let
#     compare(e) = println("$e simplifies to $(simplify(e))")
#     compare(:(0*x + C*dx))
#     compare(:(2*x^1*dx))
#     compare(:(1*x^0*dx))
# end
# ```
