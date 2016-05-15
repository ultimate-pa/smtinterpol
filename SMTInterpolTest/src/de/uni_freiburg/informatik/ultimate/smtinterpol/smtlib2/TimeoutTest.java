/*
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import java.io.StringReader;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadInfo;
import java.lang.management.ThreadMXBean;

import org.junit.Assert;
import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.ReasonUnknown;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TestCaseWithLogger;

@RunWith(JUnit4.class)
public class TimeoutTest extends TestCaseWithLogger {

	private static final String BENCHMARK =
			"(set-logic QF_UFLIA)\n(set-info :status sat)\n"
			+ "(declare-fun arg0 () Int)\n(declare-fun arg1 () Int)\n"
			+ "(declare-fun fmt0 () Int)\n(declare-fun fmt1 () Int)\n"
			+ "(declare-fun distance () Int)\n(declare-fun fmt_length () Int)\n"
			+ "(declare-fun adr_lo () Int)\n(declare-fun adr_medlo () Int)\n"
			+ "(declare-fun adr_medhi () Int)\n(declare-fun adr_hi () Int)\n"
			+ "(declare-fun format (Int) Int)\n(declare-fun percent () Int)\n"
			+ "(declare-fun s () Int)\n(declare-fun s_count (Int) Int)\n"
			+ "(declare-fun x () Int)\n(declare-fun x_count (Int) Int)\n"
			+ "(assert (let ((?v_1 (+ fmt0 1)) (?v_0 (- (- fmt1 2) fmt0)) (?v_24 (format 0))) (let ((?v_50 (= ?v_24 percent)) (?v_25 (format 1))) (let ((?v_54 (= ?v_25 percent)) (?v_51 (= ?v_25 s)) (?v_153 (= ?v_25 x)) (?v_26 (format 2))) (let ((?v_58 (= ?v_26 percent)) (?v_55 (= ?v_26 s)) (?v_156 (= ?v_26 x)) (?v_27 (format 3))) (let ((?v_62 (= ?v_27 percent)) (?v_59 (= ?v_27 s)) (?v_159 (= ?v_27 x)) (?v_28 (format 4))) (let ((?v_66 (= ?v_28 percent)) (?v_63 (= ?v_28 s)) (?v_162 (= ?v_28 x)) (?v_29 (format 5))) (let ((?v_70 (= ?v_29 percent)) (?v_67 (= ?v_29 s)) (?v_165 (= ?v_29 x)) (?v_30 (format 6))) (let ((?v_74 (= ?v_30 percent)) (?v_71 (= ?v_30 s)) (?v_168 (= ?v_30 x)) (?v_31 (format 7))) (let ((?v_78 (= ?v_31 percent)) (?v_75 (= ?v_31 s)) (?v_171 (= ?v_31 x)) (?v_32 (format 8))) (let ((?v_82 (= ?v_32 percent)) (?v_79 (= ?v_32 s)) (?v_174 (= ?v_32 x)) (?v_33 (format 9))) (let ((?v_86 (= ?v_33 percent)) (?v_83 (= ?v_33 s)) (?v_177 (= ?v_33 x)) (?v_34 (format 10))) (let ((?v_90 (= ?v_34 percent)) (?v_87 (= ?v_34 s)) (?v_180 (= ?v_34 x)) (?v_35 (format 11))) (let ((?v_94 (= ?v_35 percent)) (?v_91 (= ?v_35 s)) (?v_183 (= ?v_35 x)) (?v_36 (format 12))) (let ((?v_98 (= ?v_36 percent)) (?v_95 (= ?v_36 s)) (?v_186 (= ?v_36 x)) (?v_37 (format 13))) (let ((?v_102 (= ?v_37 percent)) (?v_99 (= ?v_37 s)) (?v_189 (= ?v_37 x)) (?v_38 (format 14))) (let ((?v_106 (= ?v_38 percent)) (?v_103 (= ?v_38 s)) (?v_192 (= ?v_38 x)) (?v_39 (format 15))) (let ((?v_110 (= ?v_39 percent)) (?v_107 (= ?v_39 s)) (?v_195 (= ?v_39 x)) (?v_40 (format 16))) (let ((?v_114 (= ?v_40 percent)) (?v_111 (= ?v_40 s)) (?v_198 (= ?v_40 x)) (?v_41 (format 17))) (let ((?v_118 (= ?v_41 percent)) (?v_115 (= ?v_41 s)) (?v_201 (= ?v_41 x)) (?v_42 (format 18))) (let ((?v_122 (= ?v_42 percent)) (?v_119 (= ?v_42 s)) (?v_204 (= ?v_42 x)) (?v_43 (format 19))) (let ((?v_126 (= ?v_43 percent)) (?v_123 (= ?v_43 s)) (?v_207 (= ?v_43 x)) (?v_44 (format 20))) (let ((?v_130 (= ?v_44 percent)) (?v_127 (= ?v_44 s)) (?v_210 (= ?v_44 x)) (?v_45 (format 21))) (let ((?v_134 (= ?v_45 percent)) (?v_131 (= ?v_45 s)) (?v_213 (= ?v_45 x)) (?v_46 (format 22))) (let ((?v_138 (= ?v_46 percent)) (?v_135 (= ?v_46 s)) (?v_216 (= ?v_46 x)) (?v_47 (format 23))) (let ((?v_142 (= ?v_47 percent)) (?v_139 (= ?v_47 s)) (?v_219 (= ?v_47 x)) (?v_48 (format 24))) (let ((?v_146 (= ?v_48 percent)) (?v_143 (= ?v_48 s)) (?v_222 (= ?v_48 x)) (?v_49 (format 25))) (let ((?v_150 (= ?v_49 percent)) (?v_147 (= ?v_49 s)) (?v_225 (= ?v_49 x)) (?v_52 (and ?v_50 ?v_51)) (?v_53 (s_count 0)) (?v_56 (and ?v_54 ?v_55)) (?v_57 (s_count 1)) (?v_60 (and ?v_58 ?v_59)) (?v_61 (s_count 2)) (?v_64 (and ?v_62 ?v_63)) (?v_65 (s_count 3)) (?v_68 (and ?v_66 ?v_67)) (?v_69 (s_count 4)) (?v_72 (and ?v_70 ?v_71)) (?v_73 (s_count 5)) (?v_76 (and ?v_74 ?v_75)) (?v_77 (s_count 6)) (?v_80 (and ?v_78 ?v_79)) (?v_81 (s_count 7)) (?v_84 (and ?v_82 ?v_83)) (?v_85 (s_count 8)) (?v_88 (and ?v_86 ?v_87)) (?v_89 (s_count 9)) (?v_92 (and ?v_90 ?v_91)) (?v_93 (s_count 10)) (?v_96 (and ?v_94 ?v_95)) (?v_97 (s_count 11)) (?v_100 (and ?v_98 ?v_99)) (?v_101 (s_count 12)) (?v_104 (and ?v_102 ?v_103)) (?v_105 (s_count 13)) (?v_108 (and ?v_106 ?v_107)) (?v_109 (s_count 14)) (?v_112 (and ?v_110 ?v_111)) (?v_113 (s_count 15)) (?v_116 (and ?v_114 ?v_115)) (?v_117 (s_count 16)) (?v_120 (and ?v_118 ?v_119)) (?v_121 (s_count 17)) (?v_124 (and ?v_122 ?v_123)) (?v_125 (s_count 18)) (?v_128 (and ?v_126 ?v_127)) (?v_129 (s_count 19)) (?v_132 (and ?v_130 ?v_131)) (?v_133 (s_count 20)) (?v_136 (and ?v_134 ?v_135)) (?v_137 (s_count 21)) (?v_140 (and ?v_138 ?v_139)) (?v_141 (s_count 22)) (?v_144 (and ?v_142 ?v_143)) (?v_145 (s_count 23))) (let ((?v_148 (and ?v_146 ?v_147)) (?v_149 (s_count 24)) (?v_228 (format 26))) (let ((?v_151 (and ?v_150 (= ?v_228 s))) (?v_152 (s_count 25)) (?v_154 (and ?v_50 ?v_153)) (?v_155 (x_count 0)) (?v_157 (and ?v_54 ?v_156)) (?v_158 (x_count 1)) (?v_160 (and ?v_58 ?v_159)) (?v_161 (x_count 2)) (?v_163 (and ?v_62 ?v_162)) (?v_164 (x_count 3)) (?v_166 (and ?v_66 ?v_165)) (?v_167 (x_count 4)) (?v_169 (and ?v_70 ?v_168)) (?v_170 (x_count 5)) (?v_172 (and ?v_74 ?v_171)) (?v_173 (x_count 6)) (?v_175 (and ?v_78 ?v_174)) (?v_176 (x_count 7)) (?v_178 (and ?v_82 ?v_177)) (?v_179 (x_count 8)) (?v_181 (and ?v_86 ?v_180)) (?v_182 (x_count 9)) (?v_184 (and ?v_90 ?v_183)) (?v_185 (x_count 10)) (?v_187 (and ?v_94 ?v_186)) (?v_188 (x_count 11)) (?v_190 (and ?v_98 ?v_189)) (?v_191 (x_count 12)) (?v_193 (and ?v_102 ?v_192)) (?v_194 (x_count 13)) (?v_196 (and ?v_106 ?v_195)) (?v_197 (x_count 14)) (?v_199 (and ?v_110 ?v_198)) (?v_200 (x_count 15)) (?v_202 (and ?v_114 ?v_201)) (?v_203 (x_count 16)) (?v_205 (and ?v_118 ?v_204)) (?v_206 (x_count 17)) (?v_208 (and ?v_122 ?v_207)) (?v_209 (x_count 18)) (?v_211 (and ?v_126 ?v_210)) (?v_212 (x_count 19)) (?v_214 (and ?v_130 ?v_213)) (?v_215 (x_count 20)) (?v_217 (and ?v_134 ?v_216)) (?v_218 (x_count 21)) (?v_220 (and ?v_138 ?v_219)) (?v_221 (x_count 22)) (?v_223 (and ?v_142 ?v_222)) (?v_224 (x_count 23)) (?v_226 (and ?v_146 ?v_225)) (?v_227 (x_count 24)) (?v_229 (and ?v_150 (= ?v_228 x))) (?v_230 (x_count 25)) (?v_2 (+ fmt0 0)) (?v_3 (+ fmt0 2)) (?v_4 (+ fmt0 3)) (?v_5 (+ fmt0 4)) (?v_6 (+ fmt0 5)) (?v_7 (+ fmt0 6)) (?v_8 (+ fmt0 7)) (?v_9 (+ fmt0 8)) (?v_10 (+ fmt0 9)) (?v_11 (+ fmt0 10)) (?v_12 (+ fmt0 11)) (?v_13 (+ fmt0 12)) (?v_14 (+ fmt0 13)) (?v_15 (+ fmt0 14)) (?v_16 (+ fmt0 15)) (?v_17 (+ fmt0 16)) (?v_18 (+ fmt0 17)) (?v_19 (+ fmt0 18)) (?v_20 (+ fmt0 19)) (?v_21 (+ fmt0 20)) (?v_22 (+ fmt0 21)) (?v_23 (+ fmt0 22))) (not (=> (and (and (and (and (and (and (and (and (and (and (and (= distance 46) (= fmt_length 26)) (= adr_lo 3)) (= adr_medlo 4)) (= adr_medhi 5)) (= adr_hi 6)) (and (and (= percent 37) (= s 115)) (= x 120))) (and (and (and (and (and (and (and (= fmt0 0) (= arg0 (- fmt0 distance))) (>= arg1 fmt0)) (< fmt1 (+ fmt0 (- fmt_length 1)))) (> fmt1 ?v_1)) (>= arg1 (+ arg0 distance))) (< arg1 (+ arg0 (+ distance (- fmt_length 4))))) (= arg1 (+ (+ arg0 (* 4 (s_count ?v_0))) (* 4 (x_count ?v_0)))))) (and (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (= fmt1 ?v_2) (= fmt1 ?v_1)) (= fmt1 ?v_3)) (= fmt1 ?v_4)) (= fmt1 ?v_5)) (= fmt1 ?v_6)) (= fmt1 ?v_7)) (= fmt1 ?v_8)) (= fmt1 ?v_9)) (= fmt1 ?v_10)) (= fmt1 ?v_11)) (= fmt1 ?v_12)) (= fmt1 ?v_13)) (= fmt1 ?v_14)) (= fmt1 ?v_15)) (= fmt1 ?v_16)) (= fmt1 ?v_17)) (= fmt1 ?v_18)) (= fmt1 ?v_19)) (= fmt1 ?v_20)) (= fmt1 ?v_21)) (= fmt1 ?v_22)) (= fmt1 ?v_23)) (= fmt1 (+ fmt0 23))) (= fmt1 (+ fmt0 24))) (= fmt1 (+ fmt0 25))) (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (= arg1 ?v_2) (= arg1 ?v_1)) (= arg1 ?v_3)) (= arg1 ?v_4)) (= arg1 ?v_5)) (= arg1 ?v_6)) (= arg1 ?v_7)) (= arg1 ?v_8)) (= arg1 ?v_9)) (= arg1 ?v_10)) (= arg1 ?v_11)) (= arg1 ?v_12)) (= arg1 ?v_13)) (= arg1 ?v_14)) (= arg1 ?v_15)) (= arg1 ?v_16)) (= arg1 ?v_17)) (= arg1 ?v_18)) (= arg1 ?v_19)) (= arg1 ?v_20)) (= arg1 ?v_21)) (= arg1 ?v_22)) (= arg1 ?v_23)))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (or (or (or (or (or (or (or ?v_50 (= ?v_24 s)) (= ?v_24 x)) (= ?v_24 3)) (= ?v_24 4)) (= ?v_24 5)) (= ?v_24 6)) (= ?v_24 255)) (or (or (or (or (or (or (or ?v_54 ?v_51) ?v_153) (= ?v_25 3)) (= ?v_25 4)) (= ?v_25 5)) (= ?v_25 6)) (= ?v_25 255))) (or (or (or (or (or (or (or ?v_58 ?v_55) ?v_156) (= ?v_26 3)) (= ?v_26 4)) (= ?v_26 5)) (= ?v_26 6)) (= ?v_26 255))) (or (or (or (or (or (or (or ?v_62 ?v_59) ?v_159) (= ?v_27 3)) (= ?v_27 4)) (= ?v_27 5)) (= ?v_27 6)) (= ?v_27 255))) (or (or (or (or (or (or (or ?v_66 ?v_63) ?v_162) (= ?v_28 3)) (= ?v_28 4)) (= ?v_28 5)) (= ?v_28 6)) (= ?v_28 255))) (or (or (or (or (or (or (or ?v_70 ?v_67) ?v_165) (= ?v_29 3)) (= ?v_29 4)) (= ?v_29 5)) (= ?v_29 6)) (= ?v_29 255))) (or (or (or (or (or (or (or ?v_74 ?v_71) ?v_168) (= ?v_30 3)) (= ?v_30 4)) (= ?v_30 5)) (= ?v_30 6)) (= ?v_30 255))) (or (or (or (or (or (or (or ?v_78 ?v_75) ?v_171) (= ?v_31 3)) (= ?v_31 4)) (= ?v_31 5)) (= ?v_31 6)) (= ?v_31 255))) (or (or (or (or (or (or (or ?v_82 ?v_79) ?v_174) (= ?v_32 3)) (= ?v_32 4)) (= ?v_32 5)) (= ?v_32 6)) (= ?v_32 255))) (or (or (or (or (or (or (or ?v_86 ?v_83) ?v_177) (= ?v_33 3)) (= ?v_33 4)) (= ?v_33 5)) (= ?v_33 6)) (= ?v_33 255))) (or (or (or (or (or (or (or ?v_90 ?v_87) ?v_180) (= ?v_34 3)) (= ?v_34 4)) (= ?v_34 5)) (= ?v_34 6)) (= ?v_34 255))) (or (or (or (or (or (or (or ?v_94 ?v_91) ?v_183) (= ?v_35 3)) (= ?v_35 4)) (= ?v_35 5)) (= ?v_35 6)) (= ?v_35 255))) (or (or (or (or (or (or (or ?v_98 ?v_95) ?v_186) (= ?v_36 3)) (= ?v_36 4)) (= ?v_36 5)) (= ?v_36 6)) (= ?v_36 255))) (or (or (or (or (or (or (or ?v_102 ?v_99) ?v_189) (= ?v_37 3)) (= ?v_37 4)) (= ?v_37 5)) (= ?v_37 6)) (= ?v_37 255))) (or (or (or (or (or (or (or ?v_106 ?v_103) ?v_192) (= ?v_38 3)) (= ?v_38 4)) (= ?v_38 5)) (= ?v_38 6)) (= ?v_38 255))) (or (or (or (or (or (or (or ?v_110 ?v_107) ?v_195) (= ?v_39 3)) (= ?v_39 4)) (= ?v_39 5)) (= ?v_39 6)) (= ?v_39 255))) (or (or (or (or (or (or (or ?v_114 ?v_111) ?v_198) (= ?v_40 3)) (= ?v_40 4)) (= ?v_40 5)) (= ?v_40 6)) (= ?v_40 255))) (or (or (or (or (or (or (or ?v_118 ?v_115) ?v_201) (= ?v_41 3)) (= ?v_41 4)) (= ?v_41 5)) (= ?v_41 6)) (= ?v_41 255))) (or (or (or (or (or (or (or ?v_122 ?v_119) ?v_204) (= ?v_42 3)) (= ?v_42 4)) (= ?v_42 5)) (= ?v_42 6)) (= ?v_42 255))) (or (or (or (or (or (or (or ?v_126 ?v_123) ?v_207) (= ?v_43 3)) (= ?v_43 4)) (= ?v_43 5)) (= ?v_43 6)) (= ?v_43 255))) (or (or (or (or (or (or (or ?v_130 ?v_127) ?v_210) (= ?v_44 3)) (= ?v_44 4)) (= ?v_44 5)) (= ?v_44 6)) (= ?v_44 255))) (or (or (or (or (or (or (or ?v_134 ?v_131) ?v_213) (= ?v_45 3)) (= ?v_45 4)) (= ?v_45 5)) (= ?v_45 6)) (= ?v_45 255))) (or (or (or (or (or (or (or ?v_138 ?v_135) ?v_216) (= ?v_46 3)) (= ?v_46 4)) (= ?v_46 5)) (= ?v_46 6)) (= ?v_46 255))) (or (or (or (or (or (or (or ?v_142 ?v_139) ?v_219) (= ?v_47 3)) (= ?v_47 4)) (= ?v_47 5)) (= ?v_47 6)) (= ?v_47 255))) (or (or (or (or (or (or (or ?v_146 ?v_143) ?v_222) (= ?v_48 3)) (= ?v_48 4)) (= ?v_48 5)) (= ?v_48 6)) (= ?v_48 255))) (or (or (or (or (or (or (or ?v_150 ?v_147) ?v_225) (= ?v_49 3)) (= ?v_49 4)) (= ?v_49 5)) (= ?v_49 6)) (= ?v_49 255)))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (=> ?v_52 (= ?v_53 1)) (=> (not ?v_52) (= ?v_53 0))) (and (=> ?v_56 (= ?v_57 (+ ?v_53 1))) (=> (not ?v_56) (= ?v_57 ?v_53)))) (and (=> ?v_60 (= ?v_61 (+ ?v_57 1))) (=> (not ?v_60) (= ?v_61 ?v_57)))) (and (=> ?v_64 (= ?v_65 (+ ?v_61 1))) (=> (not ?v_64) (= ?v_65 ?v_61)))) (and (=> ?v_68 (= ?v_69 (+ ?v_65 1))) (=> (not ?v_68) (= ?v_69 ?v_65)))) (and (=> ?v_72 (= ?v_73 (+ ?v_69 1))) (=> (not ?v_72) (= ?v_73 ?v_69)))) (and (=> ?v_76 (= ?v_77 (+ ?v_73 1))) (=> (not ?v_76) (= ?v_77 ?v_73)))) (and (=> ?v_80 (= ?v_81 (+ ?v_77 1))) (=> (not ?v_80) (= ?v_81 ?v_77)))) (and (=> ?v_84 (= ?v_85 (+ ?v_81 1))) (=> (not ?v_84) (= ?v_85 ?v_81)))) (and (=> ?v_88 (= ?v_89 (+ ?v_85 1))) (=> (not ?v_88) (= ?v_89 ?v_85)))) (and (=> ?v_92 (= ?v_93 (+ ?v_89 1))) (=> (not ?v_92) (= ?v_93 ?v_89)))) (and (=> ?v_96 (= ?v_97 (+ ?v_93 1))) (=> (not ?v_96) (= ?v_97 ?v_93)))) (and (=> ?v_100 (= ?v_101 (+ ?v_97 1))) (=> (not ?v_100) (= ?v_101 ?v_97)))) (and (=> ?v_104 (= ?v_105 (+ ?v_101 1))) (=> (not ?v_104) (= ?v_105 ?v_101)))) (and (=> ?v_108 (= ?v_109 (+ ?v_105 1))) (=> (not ?v_108) (= ?v_109 ?v_105)))) (and (=> ?v_112 (= ?v_113 (+ ?v_109 1))) (=> (not ?v_112) (= ?v_113 ?v_109)))) (and (=> ?v_116 (= ?v_117 (+ ?v_113 1))) (=> (not ?v_116) (= ?v_117 ?v_113)))) (and (=> ?v_120 (= ?v_121 (+ ?v_117 1))) (=> (not ?v_120) (= ?v_121 ?v_117)))) (and (=> ?v_124 (= ?v_125 (+ ?v_121 1))) (=> (not ?v_124) (= ?v_125 ?v_121)))) (and (=> ?v_128 (= ?v_129 (+ ?v_125 1))) (=> (not ?v_128) (= ?v_129 ?v_125)))) (and (=> ?v_132 (= ?v_133 (+ ?v_129 1))) (=> (not ?v_132) (= ?v_133 ?v_129)))) (and (=> ?v_136 (= ?v_137 (+ ?v_133 1))) (=> (not ?v_136) (= ?v_137 ?v_133)))) (and (=> ?v_140 (= ?v_141 (+ ?v_137 1))) (=> (not ?v_140) (= ?v_141 ?v_137)))) (and (=> ?v_144 (= ?v_145 (+ ?v_141 1))) (=> (not ?v_144) (= ?v_145 ?v_141)))) (and (=> ?v_148 (= ?v_149 (+ ?v_145 1))) (=> (not ?v_148) (= ?v_149 ?v_145)))) (and (=> ?v_151 (= ?v_152 (+ ?v_149 1))) (=> (not ?v_151) (= ?v_152 ?v_149))))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (=> ?v_154 (= ?v_155 1)) (=> (not ?v_154) (= ?v_155 0))) (and (=> ?v_157 (= ?v_158 (+ ?v_155 1))) (=> (not ?v_157) (= ?v_158 ?v_155)))) (and (=> ?v_160 (= ?v_161 (+ ?v_158 1))) (=> (not ?v_160) (= ?v_161 ?v_158)))) (and (=> ?v_163 (= ?v_164 (+ ?v_161 1))) (=> (not ?v_163) (= ?v_164 ?v_161)))) (and (=> ?v_166 (= ?v_167 (+ ?v_164 1))) (=> (not ?v_166) (= ?v_167 ?v_164)))) (and (=> ?v_169 (= ?v_170 (+ ?v_167 1))) (=> (not ?v_169) (= ?v_170 ?v_167)))) (and (=> ?v_172 (= ?v_173 (+ ?v_170 1))) (=> (not ?v_172) (= ?v_173 ?v_170)))) (and (=> ?v_175 (= ?v_176 (+ ?v_173 1))) (=> (not ?v_175) (= ?v_176 ?v_173)))) (and (=> ?v_178 (= ?v_179 (+ ?v_176 1))) (=> (not ?v_178) (= ?v_179 ?v_176)))) (and (=> ?v_181 (= ?v_182 (+ ?v_179 1))) (=> (not ?v_181) (= ?v_182 ?v_179)))) (and (=> ?v_184 (= ?v_185 (+ ?v_182 1))) (=> (not ?v_184) (= ?v_185 ?v_182)))) (and (=> ?v_187 (= ?v_188 (+ ?v_185 1))) (=> (not ?v_187) (= ?v_188 ?v_185)))) (and (=> ?v_190 (= ?v_191 (+ ?v_188 1))) (=> (not ?v_190) (= ?v_191 ?v_188)))) (and (=> ?v_193 (= ?v_194 (+ ?v_191 1))) (=> (not ?v_193) (= ?v_194 ?v_191)))) (and (=> ?v_196 (= ?v_197 (+ ?v_194 1))) (=> (not ?v_196) (= ?v_197 ?v_194)))) (and (=> ?v_199 (= ?v_200 (+ ?v_197 1))) (=> (not ?v_199) (= ?v_200 ?v_197)))) (and (=> ?v_202 (= ?v_203 (+ ?v_200 1))) (=> (not ?v_202) (= ?v_203 ?v_200)))) (and (=> ?v_205 (= ?v_206 (+ ?v_203 1))) (=> (not ?v_205) (= ?v_206 ?v_203)))) (and (=> ?v_208 (= ?v_209 (+ ?v_206 1))) (=> (not ?v_208) (= ?v_209 ?v_206)))) (and (=> ?v_211 (= ?v_212 (+ ?v_209 1))) (=> (not ?v_211) (= ?v_212 ?v_209)))) (and (=> ?v_214 (= ?v_215 (+ ?v_212 1))) (=> (not ?v_214) (= ?v_215 ?v_212)))) (and (=> ?v_217 (= ?v_218 (+ ?v_215 1))) (=> (not ?v_217) (= ?v_218 ?v_215)))) (and (=> ?v_220 (= ?v_221 (+ ?v_218 1))) (=> (not ?v_220) (= ?v_221 ?v_218)))) (and (=> ?v_223 (= ?v_224 (+ ?v_221 1))) (=> (not ?v_223) (= ?v_224 ?v_221)))) (and (=> ?v_226 (= ?v_227 (+ ?v_224 1))) (=> (not ?v_226) (= ?v_227 ?v_224)))) (and (=> ?v_229 (= ?v_230 (+ ?v_227 1))) (=> (not ?v_229) (= ?v_230 ?v_227))))) (and (and (and (and (and (not (= (format fmt1) percent)) (= (format (+ fmt1 1)) s)) (= (format arg1) adr_lo)) (= (format (+ arg1 1)) adr_medlo)) (= (format (+ arg1 2)) adr_medhi)) (= (format (+ arg1 3)) adr_hi))))))))))))))))))))))))))))))))))";

	public TimeoutTest() {
		super(Level.INFO);
	}

	@Test
	public void parallelTimeout() throws InterruptedException {
		Thread t1 = new Thread(new Runnable() {

			@Override
			public void run() {
				SMTInterpol solver = new SMTInterpol(Logger.getRootLogger(), false);
				solver.setOption(":timeout", 1000);
				ParseEnvironment pe = new ParseEnvironment(solver);
				pe.parseStream(new StringReader(BENCHMARK), "benchstream1");
				LBool isSat = solver.checkSat();
				Assert.assertEquals(LBool.UNKNOWN, isSat);
				Assert.assertEquals(ReasonUnknown.TIMEOUT, solver.getInfo(":reason-unknown"));
				checkNumTimeoutThreads();
				solver.exit();
			}

		});
		Thread t2 = new Thread(new Runnable() {

			@Override
			public void run() {
				SMTInterpol solver = new SMTInterpol(Logger.getRootLogger(), false);
				solver.setOption(":timeout", 1000 * 60 * 60);
				ParseEnvironment pe = new ParseEnvironment(solver);
				pe.parseStream(new StringReader(BENCHMARK), "benchstream2");
				LBool isSat = solver.checkSat();
				Assert.assertEquals(LBool.SAT, isSat);
				checkNumTimeoutThreads();
				solver.exit();
			}

		});
		t1.start();
		t2.start();
		SMTInterpol solver = new SMTInterpol(Logger.getRootLogger(), false);
		ParseEnvironment pe = new ParseEnvironment(solver);
		pe.parseStream(new StringReader(BENCHMARK), "benchstream3");
		LBool isSat = solver.checkSat();
		Assert.assertEquals(LBool.SAT, isSat);
		t1.join();
		t2.join();
		checkNumTimeoutThreads();
		solver.exit();
	}

	private void checkNumTimeoutThreads() {
		ThreadMXBean threadbean = ManagementFactory.getThreadMXBean();
		ThreadInfo[] infos = threadbean.dumpAllThreads(false, false);
		int numtohs = 0;
		for (ThreadInfo info : infos) {
			if (info.getThreadName().equals("SMTInterpol timeout thread"))
				++numtohs;
		}
		Assert.assertEquals(1, numtohs);
	}
}
