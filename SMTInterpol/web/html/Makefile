XMLFILES=$(wildcard *.xml)
DATE:=$(shell date)

all: $(addprefix gen/,$(subst .xml,.html,$(XMLFILES)))
	@find ..  -maxdepth 1 -type f | xargs cp -t gen

gen/navi.xml: file.lst $(XMLFILES) gennavi.xsl
	@mkdir -p gen
	@xsltproc -o $@ gennavi.xsl $<

gen/%.html: %.xml gen/navi.xml genpage.xsl
	@mkdir -p gen
	@xsltproc --stringparam date "${DATE}" -o $@ genpage.xsl $<

downloadpage:
	@VERSION="`git describe 2>/dev/null`" || VERSION="untagged"; \
	echo "<page id=\"download\">\n<name>Download</name>\n<content>\n<head1>License</head1>\n<txt>This program is free software; you can redistribute it and/or modify\nit under the terms of the <link\nurl=\"http://www.gnu.org/licenses/lgpl.html\">GNU Lesser General Public\nLicense</link> as published by the Free Software Foundation; either\nversion 3 of the License, or (at your option) any later version.</txt>\n\n<txt>This program is distributed in the hope that it will be useful, but\nWITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY\nor FITNESS FOR A PARTICULAR PURPOSE. See the <link\nurl=\"http://www.gnu.org/licenses/lgpl.html\">GNU Lesser General Public\nLicense</link> for more details.</txt>\n<head1>Downloads</head1>\n<txt>We provide precompiled JARs and source ZIPs.  The source ZIPs also contain the source for some samples.</txt>\n<table>\n<headrow>\n<col>Description</col>\n<col>Binary</col>\n</headrow>\n<row>\n<col>Precompiled binary (version $$VERSION)</col>\n<col><link url=\"smtinterpol.jar\">smtinterpol.jar</link><nl />(Checksums: <link url=\"smtinterpol.jar.md5\">MD5</link>, <link url=\"smtinterpol.jar.sha\">SHA 256</link>)</col>\n</row>\n<row>\n<col>Precompiled competition binary (version $$VERSION)</col>\n<col><link url=\"smtinterpol-comp.jar\">smtinterpol-comp.jar</link><nl />(Checksums: <link url=\"smtinterpol-comp.jar.md5\">MD5</link>, <link url=\"smtinterpol-comp.jar.sha\">SHA 256</link>)</col>\n</row>\n<row>\n<col>Sources (version $$VERSION)</col>\n<col><link url=\"smtinterpol-src.zip\">smtinterpol-src.zip</link><nl />(Checksums: <link url=\"smtinterpol-src.zip.md5\">MD5</link>, <link url=\"smtinterpol-src.zip.sha\">SHA 256</link>)</col>\n</row>\n</table>\n</content>\n</page>\n" > download.xml

distributable:
	$(if $(findstring undefined,$(origin FILES)), $(error "define variable FILES"))
	@mkdir -p gen
	$(foreach FILE,$(subst :, ,$(FILES)),( cp $(FILE) gen && cd gen && md5sum $(notdir $(FILE)) > $(notdir $(FILE)).md5 && sha256sum $(notdir $(FILE)) > $(notdir $(FILE)).sha );)

distribution:
	@$(MAKE) FILES=../../../smtinterpol.jar:../../../smtinterpol-src.zip:../../../smtinterpol-comp.jar distributable downloadpage
	@$(MAKE) all
	@echo "run scp SMTInterpol/web/html/gen/*.html SMTInterpol/web/html/gen/smtinterpol* <your destination>"

.PHONY: all distributable downloadpage distribution
