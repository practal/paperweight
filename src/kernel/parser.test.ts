import { displayAbsSigSpec, emptySignature } from "./signature.js";
import { defaultTerms } from "./default-terms.js";
import { parseDeclaration, parseTerm } from "./parser.js";
import { assertEqT, assertIsUndefinedT, assertT, Test } from "things";

const terms = defaultTerms;
const sig = emptySignature(terms.ids);

function parseTest(input : string, output : string | undefined) {
    const result = parseTerm(sig, terms, input, true);
    if (result === undefined || output === undefined) {
        assertIsUndefinedT(result);
        assertIsUndefinedT(output);
    } else {
        assertEqT(terms.display(result), output);
    }
}

Test(() => {
    parseTest("", undefined);
    parseTest("x, x, y => f cool: (u. x x[x, y] y[↑2, ↑1])", "x x y. f cool: (u. x x[x, y] y[↑2, x])");
    parseTest("x. x[]", "x. x[]");
    parseTest("x. x", "x. x");
    parseTest("x", "x");
}, "parseTests");

const spec = parseDeclaration(sig, terms, "x");
if (spec === undefined) console.log("Cannot parse declaration.");
else console.log("Declaration successfully parsed: ", displayAbsSigSpec(sig.ids, spec));