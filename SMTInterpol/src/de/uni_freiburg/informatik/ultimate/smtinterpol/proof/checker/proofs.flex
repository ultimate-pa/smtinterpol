/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
/* SMT-Lib lexer */
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof.checker;
import java.math.BigDecimal;
import java.math.BigInteger;
import com.github.jhoenicke.javacup.runtime.Symbol;
import com.github.jhoenicke.javacup.runtime.SimpleSymbolFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnifyHash;

/**
 * This is a autogenerated lexer for the smtlib 2 script files.
 * It is generated from smtlib.flex by JFlex.
 */
%%

%class ProofLexer
%public
%unicode
%implements com.github.jhoenicke.javacup.runtime.Scanner
%type com.github.jhoenicke.javacup.runtime.Symbol
%function next_token
%line
%column

%{
  private StringBuilder string; // NOPMD
  private SimpleSymbolFactory symFactory;
  private final UnifyHash<BigInteger> bignumbers = new UnifyHash<BigInteger>();
  private boolean version25 = true;
  
  public void setVersion25(boolean on) {
    version25 = on;
  }
  
  public boolean isVersion25() {
    return version25;
  }
  
  public void setSymbolFactory(SimpleSymbolFactory factory) {
    symFactory = factory;
  }

  private Symbol symbol(int type) {
    return symFactory.newSymbol(yytext(), type, yyline+1, yycolumn, yyline+1, yycolumn+yylength());
  }
  private Symbol symbol(int type, Object value) {
    return symFactory.newSymbol(yytext(), type, yyline+1, yycolumn, yyline+1, yycolumn+yylength(), value);
  }
  
  private BigInteger convertNumeral(String numeral) {
	BigInteger result = new BigInteger(numeral);
	int hash = result.hashCode();
	for (BigInteger integer : bignumbers.iterateHashCode(hash)) {
		if (integer.equals(result))
			return integer;
	}
	bignumbers.put(hash, result);
	return result;
  }
%}

LineTerminator = \r|\n|\r\n
InputCharacter = [^\r\n]
WhiteSpace     = {LineTerminator} | [ \t\f]

/* comments */
Comment = {EndOfLineComment}

EndOfLineComment     = ";" {InputCharacter}* {LineTerminator}?
SMTLetter = [:letter:] | [~!@$%\^&*_+\-=<>.?/] 
SMTLetterDigit = {SMTLetter} | [:digit:]

Numeral = 0 | [1-9][0-9]*
Decimal = {Numeral} "."  0* {Numeral}
HexaDecimal = "#x" [0-9a-fA-F]+
QuotedSymbol = "|" [^|]* "|"
Symbol = {SMTLetter} {SMTLetterDigit}* 
Binary = "#b" [01]+
Keyword = ":" {SMTLetterDigit}+

%state STRING20 STRING25

%%

<YYINITIAL>  {
  "("                    { return symbol(ProofSymbols.LPAR); }
  ")"                    { return symbol(ProofSymbols.RPAR); }

  "+"                    { return symbol(ProofSymbols.PLUS, yytext()); }
  "-"                    { return symbol(ProofSymbols.MINUS, yytext()); }

  /* Predefined Symbols */
  /* Terms */
  "_"                    { return symbol(ProofSymbols.UNDERSCORE, yytext()); }
  "!"                    { return symbol(ProofSymbols.BANG, yytext()); }
  "as"                   { return symbol(ProofSymbols.AS, yytext()); }
  "choose"               { return symbol(ProofSymbols.CHOOSE, yytext()); }
  "exists"               { return symbol(ProofSymbols.EXISTS, yytext()); }
  "forall"               { return symbol(ProofSymbols.FORALL, yytext()); }
  "let"                  { return symbol(ProofSymbols.LET, yytext()); }
  "match"                { return symbol(ProofSymbols.MATCH, yytext()); }

  /* proof rules */
  "assume"               { return symbol(ProofSymbols.ASSUME, yytext()); }
  "res"                  { return symbol(ProofSymbols.RES, yytext()); }
  "let-proof"            { return symbol(ProofSymbols.LETPROOF, yytext()); }
  "define-fun"           { return symbol(ProofSymbols.DEFINEFUN, yytext()); }
  "declare-fun"          { return symbol(ProofSymbols.DECLAREFUN, yytext()); }
  "oracle"               { return symbol(ProofSymbols.ORACLE, yytext()); }
  "par"                  { return symbol(ProofSymbols.PAR, yytext()); }

  /* axioms */
  "false-"               { return symbol(ProofSymbols.FALSEE, yytext()); }
  "true+"                { return symbol(ProofSymbols.TRUEI, yytext()); }
  "not+"                 { return symbol(ProofSymbols.NOTI, yytext()); }
  "not-"                 { return symbol(ProofSymbols.NOTE, yytext()); }
  "or+"                  { return symbol(ProofSymbols.ORI, yytext()); }
  "or-"                  { return symbol(ProofSymbols.ORE, yytext()); }
  "and+"                 { return symbol(ProofSymbols.ANDI, yytext()); }
  "and-"                 { return symbol(ProofSymbols.ANDE, yytext()); }
  "=>+"                  { return symbol(ProofSymbols.IMPI, yytext()); }
  "=>-"                  { return symbol(ProofSymbols.IMPE, yytext()); }
  "=+1"                  { return symbol(ProofSymbols.IFFI1, yytext()); }
  "=+2"                  { return symbol(ProofSymbols.IFFI2, yytext()); }
  "=-1"                  { return symbol(ProofSymbols.IFFE1, yytext()); }
  "=-2"                  { return symbol(ProofSymbols.IFFE2, yytext()); }
  "xor+"                 { return symbol(ProofSymbols.XORI, yytext()); }
  "xor-"                 { return symbol(ProofSymbols.XORE, yytext()); }
  "forall+"              { return symbol(ProofSymbols.FORALLI, yytext()); }
  "forall-"              { return symbol(ProofSymbols.FORALLE, yytext()); }
  "exists+"              { return symbol(ProofSymbols.EXISTSI, yytext()); }
  "exists-"              { return symbol(ProofSymbols.EXISTSE, yytext()); }

  "=+"                   { return symbol(ProofSymbols.EQI, yytext()); }
  "=-"                   { return symbol(ProofSymbols.EQE, yytext()); }
  "distinct+"            { return symbol(ProofSymbols.DISTINCTI, yytext()); }
  "distinct-"            { return symbol(ProofSymbols.DISTINCTE, yytext()); }
  "ite1"                 { return symbol(ProofSymbols.ITE1, yytext()); }
  "ite2"                 { return symbol(ProofSymbols.ITE2, yytext()); }
  "refl"                 { return symbol(ProofSymbols.REFL, yytext()); }
  "symm"                 { return symbol(ProofSymbols.SYMM, yytext()); }
  "trans"                { return symbol(ProofSymbols.TRANS, yytext()); }
  "cong"                 { return symbol(ProofSymbols.CONG, yytext()); }
  "expand"               { return symbol(ProofSymbols.EXPAND, yytext()); }
  "del!"                 { return symbol(ProofSymbols.DELANNOT, yytext()); }

  /* Arithmetic */
  "divisible-def"        { return symbol(ProofSymbols.DIVISIBLEDEF, yytext()); }
  ">def"                 { return symbol(ProofSymbols.GTDEF, yytext()); }
  ">=def"                { return symbol(ProofSymbols.GEQDEF, yytext()); }
  "trichotomy"           { return symbol(ProofSymbols.TRICHOTOMY, yytext()); }
  "total"                { return symbol(ProofSymbols.TOTAL, yytext()); }
  "total-int"            { return symbol(ProofSymbols.TOTALINT, yytext()); }
  "farkas"               { return symbol(ProofSymbols.FARKAS, yytext()); }
  "to_int-high"          { return symbol(ProofSymbols.TOINTHIGH, yytext()); }
  "to_int-low"           { return symbol(ProofSymbols.TOINTLOW, yytext()); }
  "-def"                 { return symbol(ProofSymbols.MINUSDEF, yytext()); }
  "/def"                 { return symbol(ProofSymbols.DIVIDEDEF, yytext()); }
  "poly+"                { return symbol(ProofSymbols.POLYADD, yytext()); }
  "poly*"                { return symbol(ProofSymbols.POLYMUL, yytext()); }
  "to_real-def"          { return symbol(ProofSymbols.TOREALDEF, yytext()); }
  "div-low"              { return symbol(ProofSymbols.DIVLOW, yytext()); }
  "div-high"             { return symbol(ProofSymbols.DIVHIGH, yytext()); }
  "mod-def"              { return symbol(ProofSymbols.MODDEF, yytext()); }

  /* arrays */
  "selectstore1"         { return symbol(ProofSymbols.SELECTSTORE1, yytext()); }
  "selectstore2"         { return symbol(ProofSymbols.SELECTSTORE2, yytext()); }
  "extdiff"              { return symbol(ProofSymbols.EXTDIFF, yytext()); }
  "const"                { return symbol(ProofSymbols.CONST, yytext()); }

  /* datatypes */
  "dt-project"           { return symbol(ProofSymbols.DT_PROJECT, yytext()); }
  "dt-cons"              { return symbol(ProofSymbols.DT_CONS, yytext()); }
  "dt-test+"             { return symbol(ProofSymbols.DT_TESTI, yytext()); }
  "dt-test-"             { return symbol(ProofSymbols.DT_TESTE, yytext()); }
  "dt-exhaust"           { return symbol(ProofSymbols.DT_EXHAUST, yytext()); }
  "dt-acyclic"           { return symbol(ProofSymbols.DT_ACYCLIC, yytext()); }
  "dt-match"             { return symbol(ProofSymbols.DT_MATCH, yytext()); }

  /* Predefined Keywords */
  ":named"               { return symbol(ProofSymbols.CNAMED, yytext()); }
  ":pattern"             { return symbol(ProofSymbols.CPATTERN, yytext()); }

  /* Other Symbols and Keywords */
  {QuotedSymbol}         { return symbol(ProofSymbols.SYMBOL, yytext().substring(1, yylength()-1)); }
  {Symbol}               { return symbol(ProofSymbols.SYMBOL, yytext()); }
  {Keyword}              { return symbol(ProofSymbols.KEYWORD, yytext()); }
  
  /* Numbers and Strings */
  {Numeral}              { return symbol(ProofSymbols.NUMERAL, convertNumeral(yytext())); }
  {Decimal}              { return symbol(ProofSymbols.DECIMAL, new BigDecimal(yytext())); }
  {HexaDecimal}          { return symbol(ProofSymbols.HEXADECIMAL, yytext()); }
  {Binary}               { return symbol(ProofSymbols.BINARY, yytext()); }
  \"                     { string = new StringBuilder(); yybegin(STRING25); }

 
  /* comments */
  {Comment}              { /* ignore */ }
 
  /* whitespace */
  {WhiteSpace}           { /* ignore */ }
}

<STRING25> {
  [^\"]+                         { string.append( yytext() ); }
  \"\"                           { string.append ('\"'); }
  \"                             { String value = string.toString();
                                   string = null;
                                   yybegin(YYINITIAL);
                                   return symbol(ProofSymbols.STRING, value); }
}


/* error fallback */
.|\n                             { return symbol(ProofSymbols.error, yytext()); }

<<EOF>>                          { return symbol(ProofSymbols.EOF); }