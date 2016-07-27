SHELL=/bin/bash
XMLFILES=$(wildcard *.xml)
DATE:=$(shell LANG=C date)
VERSION:=$(shell git describe 2>/dev/null || echo untagged)
OTHERFILES := valid-xhtml10.png vcss.gif smtinterpol.css goedel.jpg floc2014.jpg
SMT2FILES := usage.smt2 unsat.smt2 subannot.smt2 interpolation.smt2
JARFILES := smtinterpol-$(VERSION).jar smtinterpol-$(VERSION)-sources.jar

CHECKSUMS = $(patsubst %,gen/%.sha,$(JARFILES) $(SMT2FILES))


# mccarthy1.smt2 mccarthy2.smt2
# UsageStub.java InterpolationUsageStub.java \
# fmcad11.tar.bz2 interpolations.tar.bz2


all: $(addprefix gen/,$(subst .xml,.html,$(XMLFILES))) $(CHECKSUMS)
all: $(addprefix gen/,$(OTHERFILES))

$(addprefix gen/,$(JARFILES)): gen/%: ../../../dist/%
	cp $< $@

$(addprefix gen/,$(OTHERFILES) $(SMT2FILES)): gen/%: ../%
	cp $< $@

$(CHECKSUMS): gen/%.sha: gen/%
	cd gen; sha256sum $* > $*.sha

clean:
	@rm -rf gen

gen/navi.xml: file.lst $(XMLFILES) gennavi.xsl
	@mkdir -p gen
	xsltproc -o $@ gennavi.xsl $<

gen/%.html: %.xml gen/navi.xml genpage.xsl
	@mkdir -p gen
	xsltproc --stringparam version "$(VERSION)" --stringparam date "$(DATE)" -o $@ genpage.xsl $<

distribution: clean all
	@echo "run scp SMTInterpol/web/html/gen/* <your destination>"

.PHONY: all distclean distributable downloadpage distribution
