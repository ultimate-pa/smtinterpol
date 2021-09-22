<?xml version="1.0" encoding="UTF-8"?>

<xsl:stylesheet version="1.0"
xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns="http://www.w3.org/1999/xhtml">

  <xsl:template match="node() | @*">
    <xsl:copy-of select="."/>
  </xsl:template>

  <xsl:output
      method = "xml"
      encoding = "UTF-8"
      omit-xml-declaration = "yes"
      indent = "yes" />

  <xsl:template match="/page">
    <xsl:text disable-output-escaping="yes">&lt;!DOCTYPE html&gt;&#10;</xsl:text>
    <html xmlns="http://www.w3.org/1999/xhtml" xml:lang="en-us" lang="en-us">
      <head>
	<xsl:element name="meta">
	  <xsl:attribute name="http-equiv">Content-Type</xsl:attribute>
	  <xsl:attribute name="content">text/html; charset=UTF-8</xsl:attribute>
	</xsl:element>
	<xsl:element name="meta">
	  <xsl:attribute name="name">robots</xsl:attribute>
	  <xsl:attribute name="content">index, follow</xsl:attribute>
	</xsl:element>
	<xsl:element name="meta">
	  <xsl:attribute name="name">keywords</xsl:attribute>
	  <xsl:attribute name="content">SMTInterpol, Craig, Interpolation, Tool, SMT, solver</xsl:attribute>
	</xsl:element>
	<xsl:element name="meta">
	  <xsl:attribute name="name">title</xsl:attribute>
	  <xsl:attribute name="content">SMTInterpol Version 2.0</xsl:attribute>
	</xsl:element>
	<xsl:element name="meta">
	  <xsl:attribute name="name">description</xsl:attribute>
	  <xsl:attribute name="content">The interpolating SMT solver SMTInterpol</xsl:attribute>
	</xsl:element>
	<xsl:element name="meta">
	  <xsl:attribute name="name">generator</xsl:attribute>
	  <xsl:attribute name="content">The SMTInterpol Team</xsl:attribute>
	</xsl:element>
	<xsl:element name="meta">
	  <xsl:attribute name="name">viewport</xsl:attribute>
	  <xsl:attribute name="content">width=device-width, initial-scale=1</xsl:attribute>
	</xsl:element>
	<xsl:element name="link">
	  <xsl:attribute name="rel">stylesheet</xsl:attribute>
	  <xsl:attribute name="href">smtinterpol.css</xsl:attribute>
	  <xsl:attribute name="type">text/css</xsl:attribute>
	</xsl:element>
	<title>SMTInterpol - an Interpolating SMT Solver</title>
      </head>
      <body>
	<a class="skip" href="#main">Skip navigation</a>
	<header>
	  <div id="logo">
	    <h1>SMTInterpol</h1>
	    <h2>an Interpolating SMT Solver</h2>
	  </div>
	  <nav><ul id="subnav">
	    <xsl:variable name="myId" select="//page/@id" />
	    <xsl:for-each select="document('gen/navi.xml')/navi/subpage">
	      <xsl:choose>
		<xsl:when test="@id=$myId">
		  <li><div><xsl:copy-of select="name/text()" /></div></li>
		</xsl:when>
		<xsl:otherwise>
		  <li>
		    <xsl:element name="a">
		      <xsl:attribute name="href">
			<xsl:value-of select="link/text()" disable-output-escaping="yes" />
		      </xsl:attribute>
		      <xsl:copy-of select="name/text()" />
		    </xsl:element>
		  </li>
		</xsl:otherwise>
	      </xsl:choose>
	    </xsl:for-each>
            <li>
              <a href="online/">Web Interface</a>
	    </li>
	  </ul></nav>
	</header>
	<div id="main">
	  <xsl:apply-templates match="content" />
	</div>
	<footer>
	  <p>
	    Last modified: <xsl:value-of select="$date" />
	    <xsl:text disable-output-escaping="yes">&amp;nbsp;</xsl:text>
	    <xsl:text disable-output-escaping="yes">&amp;nbsp;</xsl:text>
	    <xsl:text disable-output-escaping="yes">&amp;nbsp;</xsl:text>
	    <a href="https://validator.w3.org/check?uri=referer" referrerpolicy="no-referrer-when-downgrade">
	      <img src="HTML5_Logo.svg"
		   alt="Valid HTML 5" height="32" width="23" />
            </a>
	    <xsl:text disable-output-escaping="yes">&amp;nbsp;</xsl:text>
	    <a href="https://jigsaw.w3.org/css-validator/check/referer" referrerpolicy="no-referrer-when-downgrade">
	      <img src="CSS3_Logo.svg"
		   alt="Valid CSS!" height="32" width="23" />
	    </a>
	  </p>
	</footer>
      </body>
    </html>
  </xsl:template>

  <xsl:template match="name" />
  
  <xsl:template match="ref">
    <div>
      <xsl:element name="a">
	<xsl:attribute name="href">
	  <xsl:value-of select="text()" disable-output-escaping="yes" />
	</xsl:attribute>
	<xsl:attribute name="target">_blank</xsl:attribute>
	<xsl:copy-of select="//name/text()" /> (external link)
      </xsl:element>
    </div>
  </xsl:template>

  <xsl:template match="content">
    <xsl:apply-templates />
  </xsl:template>

  <xsl:template match="head1">
    <h1>
      <xsl:apply-templates />
    </h1>
  </xsl:template>

  <xsl:template match="head2">
    <h2>
      <xsl:apply-templates />
    </h2>
  </xsl:template>

  <xsl:template match="txt">
    <div>
      <xsl:apply-templates />
    </div>
  </xsl:template>

  <xsl:template match="b">
    <b>
      <xsl:apply-templates />
    </b>
  </xsl:template>

  <xsl:template match="link">
    <xsl:element name="a">
      <xsl:attribute name="href">
	<xsl:value-of select="./@url" />
      </xsl:attribute>
      <xsl:apply-templates />
    </xsl:element>
  </xsl:template>

  <xsl:template match="table">
    <table>
      <xsl:apply-templates />
    </table>
  </xsl:template>

  <xsl:template match="headrow">
    <tr class="headrow">
      <xsl:apply-templates />
    </tr>
  </xsl:template>

  <xsl:template match="row">
    <tr>
      <xsl:apply-templates />
    </tr>
  </xsl:template>

  <xsl:template match="col"> 
    <td>
      <xsl:apply-templates />
    </td>
  </xsl:template>

  <xsl:template match="img">
    <xsl:element name="img">
      <xsl:attribute name="src">
	<xsl:value-of select="./@src" disable-output-escaping="yes" />
      </xsl:attribute>
      <xsl:attribute name="alt">
	<xsl:value-of select="./@alt" disable-output-escaping="yes" />
      </xsl:attribute>
    </xsl:element>
  </xsl:template>

  <xsl:template match="verb">
    <pre>
      <xsl:apply-templates />
    </pre>
  </xsl:template>

  <xsl:template match="s">
    <span style="font-variant: small-caps;">SMTInterpol</span>
  </xsl:template>

  <xsl:template match="tt">
    <code>
      <xsl:apply-templates />
    </code>
  </xsl:template>

  <xsl:template match="emph">
    <em>
      <xsl:apply-templates />
    </em>
  </xsl:template>

  <xsl:template match="nl">
    <br />
  </xsl:template>

  <xsl:template match="version">
    <xsl:value-of select="$version" />
  </xsl:template>

  <xsl:template match="versionlink">
    <a href="smtinterpol-{$version}{@suffix}.jar">smtinterpol-<xsl:value-of select="$version" /><xsl:value-of select="@suffix" />.jar</a><br />(Checksum: <a href="smtinterpol-{$version}{@suffix}.jar.sha">SHA 256</a>)
  </xsl:template>

  <xsl:template match="downloads">
    <table>
      <tr class="headrow">
	<td>Benchmark</td>
	<td>Description</td>
	<td>Download</td>
      </tr>
      <xsl:apply-templates />
    </table>
  </xsl:template>

  <xsl:template match="download">
    <tr>
      <td><xsl:value-of select="./@file" /></td>
      <td><xsl:apply-templates /></td>
      <td><xsl:element name="a">
	<xsl:attribute name="href">
	  <xsl:value-of select="./@file" disable-output-escaping="yes" />
	</xsl:attribute>	
	<xsl:value-of select="./@file" />
      </xsl:element>
      <br />
      (Checksum:
      <xsl:element name="a">
	<xsl:attribute name="href">
	  <xsl:value-of select="./@file" disable-output-escaping="yes" />.sha</xsl:attribute>	
	SHA 256
      </xsl:element>)</td>
    </tr>
  </xsl:template>

  <xsl:template match="desc">
    <xsl:apply-templates />
  </xsl:template>

  <xsl:template match="list">
    <ul>
      <xsl:apply-templates />
    </ul>
  </xsl:template>

  <xsl:template match="paper">
    <xsl:element name="li">
      <xsl:apply-templates select="authors" />
      <xsl:apply-templates select="title" />
      <xsl:apply-templates select="./@conf" />
      <xsl:apply-templates select="pdf" />
      <xsl:apply-templates select="doi" />
      <xsl:apply-templates select="bib" />
      <xsl:apply-templates select="arxiv" />
    </xsl:element>
  </xsl:template>

  <xsl:template match="authors">
    <xsl:value-of select="./text()" />
    <xsl:text>. </xsl:text>
  </xsl:template>

  <xsl:template match="title">
    <xsl:value-of select="./text()" />
    <xsl:text>. </xsl:text>
  </xsl:template>

  <xsl:template match="@conf">
    <xsl:text> In </xsl:text><xsl:value-of select="." /><xsl:apply-templates select="../@note" /><xsl:text>. </xsl:text>
  </xsl:template>

  <xsl:template match="@note">
    <xsl:text> </xsl:text><em><xsl:value-of select="." /></em>
  </xsl:template>

  <xsl:template match="pdf">
    <xsl:text> [</xsl:text>
    <xsl:element name="a">
      <xsl:attribute name="href"><xsl:value-of select="./text()" /></xsl:attribute>
      <xsl:text>pdf</xsl:text>
    </xsl:element>
    <xsl:text>] </xsl:text>
  </xsl:template>

  <xsl:template match="bib">
    <xsl:text> [</xsl:text>
    <xsl:element name="a">
      <xsl:attribute name="href"><xsl:value-of select="./text()" /></xsl:attribute>
      <xsl:text>bib</xsl:text>
    </xsl:element>
    <xsl:text>] </xsl:text>
  </xsl:template>

  <xsl:template match="doi">
    <xsl:text> [</xsl:text>
    <xsl:element name="a">
      <xsl:attribute name="href"><xsl:value-of select="./text()" /></xsl:attribute>
      <xsl:text>doi</xsl:text>
    </xsl:element>
    <xsl:text>] </xsl:text>
  </xsl:template>
  
  <xsl:template match="arxiv">
    <xsl:text> Authors' version at </xsl:text>
    <xsl:element name="a">
      <xsl:attribute name="href"><xsl:value-of select="./text()" /></xsl:attribute>
      <xsl:text>arXiv</xsl:text>
    </xsl:element>
    <xsl:text>.</xsl:text>
  </xsl:template>

</xsl:stylesheet>
    
    
