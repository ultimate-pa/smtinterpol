ace.define("ace/mode/smtlib_highlight_rules",["require","exports","module","ace/lib/oop","ace/mode/text_highlight_rules"], function(require, exports, module) {
"use strict";

var oop = require("../lib/oop");
var TextHighlightRules = require("./text_highlight_rules").TextHighlightRules;

var SmtlibHighlightRules = function() {
    var keywordControl = "let|exists|forall|as|_|!|match";
    var keywordOperator = "assert|check-sat|check-sat-assuming|declare-const|declare-datatype|declare-datatypes|declare-fun|declare-sort|define-fun|define-sort|echo|exit|get-assertions|get-assignment|get-info|get-interpolants|get-model|get-option|get-proof|get-unsat-core|get-unsat-assumptions|get-value|push|pop|reset|set-info|set-logic|set-option";
    var constantLanguage = "true|false|and|or|not|=>|=|distinct|xor|ite|\+|\*|/|-|mod|div|divisible|abs|to_real|to_int|is_int|<|>|<=|>=|select|store|Real|Int|Array";
    var keywordMapper = this.createKeywordMapper({
        "keyword.control": keywordControl,
        "keyword.operator": keywordOperator,
        "constant.language": constantLanguage
    }, "identifier", true);

    this.$rules = 
        {
    "start": [
        {
            token : "comment",
            regex : ";.*$"
        },
        {
            token : "constant.keyword",
            regex : ":[0-9a-zA-Z-]+\\b"
        }, 
        {
            token : "constant.numeric", // hex
            regex : "#x[0-9a-fA-F]+\\b"
        }, 
        {
            token : "constant.numeric", // binary
            regex : "#b[0-1]+\\b"
        }, 
        {
            token : "constant.numeric", // float
            regex : "\\d+(\\.\\d*)?\\b"
        },
        {
            token : keywordMapper,
            regex : "[:A-Za-z~!@$%^&*_+=<>.?-][0-9A-Za-z~!@$%^&*_+=<>.?-]*"
        },
        {
            token : "identifier",
            regex : "\\|",
            next : "quoted"
        },
        {
            token : "string",
            regex : '"',
            next : "string"
        },
    ],
    "string" : [
        {
            token : "string",
            regex : '""',
        }, {
            token : "string",
            regex : '"',
            next : "start"
        }, {
            defaultToken : "string"
        }
    ],
    "quoted" : [
        {
            token : "identifier",
            regex : "\\|",
            next : "start"
        }, {
            defaultToken : "identifier"
        }
    ]
};

};

oop.inherits(SmtlibHighlightRules, TextHighlightRules);

exports.SmtlibHighlightRules = SmtlibHighlightRules;
});

ace.define("ace/mode/smtlib",["require","exports","module","ace/lib/oop","ace/mode/text","ace/mode/smtlib_highlight_rules"], function(require, exports, module) {
"use strict";

var oop = require("../lib/oop");
var TextMode = require("./text").Mode;
var SmtlibHighlightRules = require("./smtlib_highlight_rules").SmtlibHighlightRules;

var Mode = function() {
    this.HighlightRules = SmtlibHighlightRules;
    this.$behaviour = this.$defaultBehaviour;
};
oop.inherits(Mode, TextMode);

(function() {
       
    this.lineCommentStart = ";";
    
    this.$id = "ace/mode/smtlib";
}).call(Mode.prototype);

exports.Mode = Mode;
});                (function() {
                    ace.require(["ace/mode/smtlib"], function(m) {
                        if (typeof module == "object" && typeof exports == "object" && module) {
                            module.exports = m;
                        }
                    });
                })();
            
