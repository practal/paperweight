import { ExprGrammar, SHOW_CONFLICTS, altP, charP, flatListResults, literalP, lookaheadP, lrP,  mkTerminalParsers,  optP,  orP,  recursiveP,  rep1P,  repP,  rule, seqP, showLRConflicts, tagP } from "@practal/parsing";
import { anyCharP, bobP, createRXParseEnvironment, E, owsP, runDeterministicRXParser, RXDocument, startOfRXDocument, textOfRXLine } from "@practal/rx";
import { P, R, RXPos, TAG, anyBlockP, anyLineP, blockCloseP, blockOpenP, bolP, charTestP, debugP, firstLongestP, longestP, newlineP,  unicodeLetterP, wsP } from "@practal/rx";
import { isDigit } from "things";
import { AbsSigSpec, Signature, specOfAbsSig } from "./signature.js";
import { TermKind, Terms } from "./terms.js";
import { absSigOfAbsApp } from "./validate.js";
import { identifierP, IdentifierTag } from "./identifier-parser.js";
//import { debug } from "things";

//showLRConflicts(SHOW_CONFLICTS.full);

export enum TermTag {
    id = IdentifierTag.id,
    defaultId = "defaultId",
    absid = "absid",
    varid = "varid",
    bound = "bound",
    varapp = "varapp",
    invalid = "invalid",
    unparsed = "unparsed",
    binders = "binders",
    label = "label",
    term = "term",
    terms = "terms",
    template = "template",
    templates = "templates",
    absapp = "absapp",
    absargs = "absargs",
    declaration = "declaration",
    plus = "plus",
    app = "app",
    block = "block",
    blocks = "blocks",
    line = "line",
    comment = "comment"
}


//const identifierP : P = tagP(TermTag.id, seqP(unicodeLetterP), rep1P(unicodeLetterP));
//const defaultIdP : P = tagP(TermTag.defaultId, literalP("$"));

const boundP : P = tagP(TermTag.bound, seqP(literalP("↑"), rep1P(charTestP(isDigit))));

const ows = "ows";
const ws = "ws";

function grammarFor(start : "Template" | "Declaration") : ExprGrammar {
    const g : ExprGrammar = { 
        start : "Start",
        
        rules : [
            rule("Start", start),

            rule("Term", "Expr"),

            rule("Expr", "PlusExprLevel"),

            rule("PlusExprLevel", "PreApp"),
            //rule("PlusExprLevel", "PlusExpr"),
            //rule("PlusExpr", "PlusExprLevel", ows, "plus", ws, "PreApp"),

            rule("PreApp", "AppLevel"),
            rule("PreApp", "AbsApp"),

            rule("AppLevel", "Atomic"),
            rule("AppLevel", "AppExpr"),
            rule("AppExpr", "AppLevel",  "TemplateInBrackets"),
            
            rule("Declaration", "DeclAbsId"),
            rule("Declaration", "AbsApp"),

            rule("Atomic", "id"),
            rule("Atomic", "bound"),
            rule("Atomic", "VarApp"),
            rule("Atomic", "TemplateInBrackets"),
            rule("Atomic", "blocks"),

            rule("AbsApp", "AbsId", "AbsArgs"),
            rule("AbsId", "id", ws),
            
            rule("DeclAbsId", "id"),
            //rule("AbsId", "defaultId", ows),

            rule("Arg", "AppLevel"),
            rule("Arg", "label"),
            
            rule("AbsArgsList", "Arg"),
            rule("AbsArgsList", "AbsArgsList", ws, "Arg"),

            rule("AbsArgs", "AbsArgsList"),

            rule("VarApp", "varappOpen", ows, "Terms", ows, "squareClose"),
            rule("VarApp", "varappOpen", ows, "squareClose"),

            rule("Terms", "Term"),
            rule("Terms", "Terms", ows, "comma", ws, "Term"),

            rule("TemplateOnly", "binders", ws, "Term"),

            rule("Template", "Term"),
            rule("Template", "TemplateOnly"),

            rule("TemplateInBrackets", "open", ows, "Template", ows, "close"),
            //rule("TemplatesInBrackets", "open", ows, "close"),

            //rule("Templates", "Template"),
            //rule("Templates", "Templates", ows, "comma", ows, "Template"),

        ],

        distinct : [
            [
                "id",
                //"defaultId",
                "varappOpen",
                "squareClose",
                "comma",
                //"plus",
                "label",
                "binders",
                "open",
                "close",
                "bound",
                "blocks",
                ws
            ],
        ],

        empty : [[ows, ws]]

    };
    return g;
}

const template_grammar = grammarFor("Template");
const declaration_grammar = grammarFor("Declaration");

const dotP : P = orP(literalP("."), literalP("=>"));

const commaP : P = literalP(",");

//const plusP : P = literalP("+");

const roundOpenP : P = literalP("(");
const roundCloseP : P = literalP(")");

const squareCloseP : P = literalP("]");
const squareOpenP : P = literalP("[");

const varappOpenP : P = seqP(tagP(TermTag.varid, identifierP), squareOpenP);

const blockP : P = anyBlockP(TermTag.block, TermTag.line);
const blocksP : P = tagP(TermTag.blocks, rep1P(blockP));

const commentP : P = tagP(TermTag.comment, seqP(literalP("//"), repP(anyCharP)));

const WSP : P = orP(rep1P(orP(wsP, commentP)), bolP(), bobP());
export const OWSP : P = optP(WSP);

const binderP : P = identifierP;
const bindersCommaSeparated : P = seqP(binderP, repP(OWSP, commaP, OWSP, binderP), OWSP, dotP);
const bindersWsSeparated : P = seqP(binderP, repP(OWSP, binderP), OWSP, dotP);
const bindersP : P = tagP(TermTag.binders, orP(bindersCommaSeparated, bindersWsSeparated));

const labelP : P = tagP(TermTag.label, seqP(identifierP, literalP(":")));

function terminalParsers()  {
    return mkTerminalParsers([
        ["binders", bindersP],
        ["label", labelP],
        ["varappOpen", varappOpenP],
        ["id", identifierP],
        ["bound", boundP],
        //["defaultId", defaultIdP],
        ["squareClose", squareCloseP],
        ["open", roundOpenP],
        ["close", roundCloseP],
        //["plus", plusP],
        ["comma", commaP],
        ["blocks", blocksP],
        ["ws", WSP],
        ["ows", OWSP], // This one must be last, as it could parse the empty string
    ]); 
}

const nonterminalTags : [string, string][] = [
    ["Term", TermTag.term],
    ["Declaration", TermTag.declaration],
    ["AbsApp", TermTag.absapp],
    ["AbsArgs", TermTag.absargs],
    ["AbsId", TermTag.absid],
    ["DeclAbsId", TermTag.absid],    
    ["VarApp", TermTag.varapp],
    ["TemplateOnly", TermTag.template],
    ["TemplatesInBrackets", TermTag.templates],
    ["PlusExpr", TermTag.plus],
    ["AppExpr", TermTag.app]
];

const template_lr = 
    lrP(template_grammar, nonterminalTags, terminalParsers(), TermTag.invalid);

const templateP : P = template_lr.longest_valid_prefix;
//export const templateLongestP : P = template_lr.longest_prefix;

const declaration_lr = 
    lrP(declaration_grammar, nonterminalTags, terminalParsers(), TermTag.invalid);

const declarationP : P = declaration_lr.longest_valid_prefix;

function log(s : string) {
    console.log(s);
}

if (template_lr.conflicts.size > 0) {
    log("There are " + template_lr.conflicts.size + " conflicts in template grammar.");
    for (const conflict of template_lr.conflicts) {
        log("Conflict symbol: " + conflict);
    }
} else {
    log("No template grammar conflicts found.");
}

if (declaration_lr.conflicts.size > 0) {
    log("There are " + declaration_lr.conflicts.size + " conflicts in declaration grammar.");
    for (const conflict of declaration_lr.conflicts) {
        log("Conflict symbol: " + conflict);
    }
} else {
    log("No declaration grammar conflicts found.");
}



function parseTermWith<Id, Term>(parser : P, sig : Signature<Id>, 
    terms : Terms<Id, Term>, term : string, suppressErrors : boolean = false) : Term | undefined 
{
    const parseResult = runDeterministicRXParser(term, seqP(blockOpenP, owsP, parser, owsP, blockCloseP));
    if (parseResult === undefined) return undefined;
    if (parseResult.pruned.length !== 1) return undefined;
    const env = parseResult.env;
    const pruned = parseResult.pruned[0];
    
    function childrenOf(result : R) : R[] {
        if (result.children.length !== 1) 
            throw new Error("Ambiguity in '" + result.type + "' detected.");
        return result.children[0];
    }
    
    function select(result : R, tag : TermTag) : R[] {
        const children = childrenOf(result);
        const selected : R[] = [];
        for (const child of children) {
            if (child.type === tag) selected.push(child);
        }
        return selected;
    }
    
    function select1(result : R, tag : TermTag) : R {
        const children = select(result, tag);
        if (children.length !== 1) 
            throw new Error("select1 " + tag + " failed, found " + children.length + " candidates");
        return children[0];
    }
    
    function selectUniqueChild(result : R) : R {
        const children = childrenOf(result);
        if (children.length !== 1) 
            throw new Error("Unique child expected, found " + children.length + " children in '" + result.type);
        return children[0];
    }
    
    function expect(result : R, tag : TermTag) {
        if (result.type !== tag) 
            throw new Error("Eexpected tag '" + tag + "', found tag '" + result.type + "'");
    }
    
    function convertId(result : R) : Id {
        expect(result, TermTag.id);
        const name = textOfRXLine(env.document, result.start, result.end);
        return terms.mkId(name);
    }
    
    const localVariables : Id[] = [];
    function pushBinders(binders : Id[]) {
        localVariables.push(...binders.toReversed());
    }
    function popBinders(binders : Id[]) {
        for (const _ of binders) localVariables.pop();
    }
    
    function convertTemplate(result : R) : Term {
        expect(result, TermTag.template);
        const binders = select1(result, TermTag.binders);
        const ids = select(binders, TermTag.id).map(convertId);
        const term = select1(result, TermTag.term);
        pushBinders(ids);
        const body = convert(term);
        popBinders(ids);
        return terms.mkTemplate(ids, body);
    }
    
    function convertAbsArgs(absId : Id, result : R) : [Id, Term[]][] {
        expect(result, TermTag.absargs);
        const nameAndArgs : [Id, Term[]][] = [[absId, []]];
        for (const child of childrenOf(result)) {
            if (child.type === TermTag.label) {
                const label = convertId(select1(child, TermTag.id));
                nameAndArgs.push([label, []]);
            } else {
                const arg = convert(child);
                const args = nameAndArgs[nameAndArgs.length - 1][1];
                args.push(arg);
            }
        }
        return nameAndArgs;
    }
    
    function convertAbsApp(result : R) : Term {
        expect(result, TermTag.absapp);
        const absId = select1(result, TermTag.absid);
        const id = convertId(selectUniqueChild(absId));
        const absArgs = select1(result, TermTag.absargs);
        return terms.mkAbsApp(convertAbsArgs(id, absArgs));
    }
    
    function convertStandaloneAbsId(result : R) : Term {
        expect(result, TermTag.absid);
        const id = convertId(selectUniqueChild(result));
        return terms.mkAbsApp([[id, []]]);
    }
    
    
    function convertVarApp(result : R) : Term {
        expect(result, TermTag.varapp);
        const varid = convertId(selectUniqueChild(select1(result, TermTag.varid)));
        const args = select(result, TermTag.term).map(convertTerm);
        return terms.mkVarApp(varid, args);
    }
    
    function convertTerm(result : R) : Term {
        expect(result, TermTag.term);
        const child = selectUniqueChild(result);
        return convert(child);
    }

    function convertDeclaration(result : R) : Term {
        expect(result, TermTag.declaration);
        const child = selectUniqueChild(result);
        return convert(child);
    }
    
    function resolveId(id : Id) : Term {
        for (let i = 0; i < localVariables.length; i++) {
            if (terms.ids.equal(id, localVariables[localVariables.length - i - 1]))
                return terms.mkBoundVar(i);
        }
        if (sig.isDeclared([[id, []]]))
            return terms.mkAbsApp([[id, []]]);
        else
            return terms.mkVarApp(id, []);
    }
    
    function convertBound(result : R) : Term {
        expect(result, TermTag.bound);
        const text = textOfRXLine(env.document, result.start, result.end);
        if (text.startsWith("↑")) {
            return terms.mkBoundVar(Number.parseInt(text.substring(1)));
        } else 
            throw new Error("Unknown syntax for bound variable: '" + text + "'");
    }
    
    function convert(result : R) : Term {
        switch (result.type) {
            case TermTag.template: return convertTemplate(result);
            case TermTag.term: return convertTerm(result);
            case TermTag.declaration: return convertDeclaration(result);
            case TermTag.absapp: return convertAbsApp(result);
            case TermTag.varapp: return convertVarApp(result);
            case TermTag.id: return resolveId(convertId(result));
            case TermTag.bound: return convertBound(result);
            case TermTag.absid: return convertStandaloneAbsId(result);
            case TermTag.invalid: throw new Error("Invalid term.");
            default: throw new Error("convert not implemented: " + result.type);
        }
    }
    
    try {
        return convert(pruned);
    } catch (error) {
        if (!suppressErrors) {
            env.displayResult(pruned, s => console.log(s));
            console.log(error);
        }
        return undefined;
    }
}

export function parseTerm<Id, Term>(sig : Signature<Id>, 
    terms : Terms<Id, Term>, term : string, suppressErrors : boolean = false) : Term | undefined 
{
    return parseTermWith(templateP, sig, terms, term, suppressErrors);
}
        
export function parseDeclaration<Id, Term>(sig : Signature<Id>, 
    terms : Terms<Id, Term>, declaration : string, 
    suppressErrors : boolean = false) : AbsSigSpec<Id> | undefined 
{
    const term = parseTermWith(declarationP, sig, terms, declaration, suppressErrors);
    if (term === undefined) return undefined;
    if (terms.termKindOf(term) !== TermKind.absapp) return undefined;
    const absapp = terms.destAbsApp(term);
    return specOfAbsSig(absSigOfAbsApp(terms, absapp)); // sloppy, improve later
}
