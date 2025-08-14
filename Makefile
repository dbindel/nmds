DEST=cslinux:/people/dsb253/nmds
LDOC=lua ldoc/ldoc.lua

LDOC_QMD= \
	ldoc/matcher.qmd

ldoc/%.qmd: src/%.jl
	$(LDOC) -l sh -highlight julia -p quarto -o $@ $^

.PHONY: preview render deploy clean

preview: $(LDOC_QMD)
	quarto preview

render: $(LDOC_QMD)
	quarto render

deploy:
	( rsync -avzL docs/ $(DEST) || true )

clean:
	rm -rf docs
