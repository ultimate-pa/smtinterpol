SHELL=/bin/bash
XMLFILES=docu.xml download.xml examples.xml index.xml news.xml proof-format.xml proofs.xml publications.xml
DATE:=$(shell LANG=C date)
VERSION:=$(shell git describe 2>/dev/null || echo untagged)
OTHERFILES := HTML5_Logo.svg CSS3_Logo.svg smtinterpol.css goedel.jpg floc2014.jpg floc2018.jpg
SMT2FILES := usage.smt2 unsat.smt2 subannot.smt2 interpolation.smt2 mccarthy1.smt2 mccarthy2.smt2
JARFILES := smtinterpol-$(VERSION).jar smtinterpol-$(VERSION)-sources.jar

PROOF_DOC=intro.md eq_diamond2-proof.md grammar.md lowlevel-calculus.md equality.md theory-extensions.md
PANDOCOPT=--mathml -t html5

# UsageStub.java InterpolationUsageStub.java \
# fmcad11.tar.bz2 interpolations.tar.bz2


all: $(addprefix web/,$(subst .xml,.html,$(XMLFILES)))
all: $(addprefix web/,$(SMT2FILES) $(OTHERFILES))



proof-doc/proof-format.html: $(addprefix proof-doc/,$(PROOF_DOC))
	cat $^ | pandoc $(PANDOCOPT) -o $@
proof-format.xml: proof-doc/header.xml proof-doc/proof-format.html proof-doc/footer.xml
	cat $^ > $@

$(addprefix web/,$(JARFILES)): web/%: ../../../dist/%
	@mkdir -p web
	cp $< $@

$(addprefix web/,$(OTHERFILES) $(SMT2FILES)): web/%: ../%
	@mkdir -p web
	cp $< $@

gen/hashes.xml: $(addprefix web/,$(JARFILES))
	@mkdir -p gen
	@echo '<hashes>' > $@
	@for i in $(JARFILES); do \
		echo '  <file path="'$$i'" sha256="'$$(sha256sum web/$$i | cut -d' ' -f1)'"/>' >> $@ ; \
	done
	@echo '</hashes>' >> $@

clean:
	@rm -rf gen web proof-format.xml

gen/navi.xml: file.lst $(XMLFILES) gennavi.xsl
	@mkdir -p gen
	xsltproc -o $@ gennavi.xsl $<

web/%.html: %.xml gen/navi.xml gen/hashes.xml genpage.xsl
	@mkdir -p web
	xsltproc --stringparam version "$(VERSION)" --stringparam date "$(DATE)" -o $@ genpage.xsl $<

distribution: clean all
	@echo "run scp SMTInterpol/web/html/web/* <your destination>"

.PHONY: all distclean distributable downloadpage distribution
