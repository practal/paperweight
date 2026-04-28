import { beginTheory, assume, endTheory, bind, have, S, subst, Thm } from "../workbench.js";

beginTheory();
have("Example-13", "t", ["x. x"], proveExample13());
endTheory("Example-13");

function proveExample13(): Thm {
    // Step 1: x / x  by Assume
    const step1 = assume("x");
    // Step 2: (x. x) / x  by Bind — turn term premise into template premise
    const step2 = bind("x", "x. x", step1);
    // Step 3: (x. x) / t  by Subst with x → t
    return subst(S("x", "t"), step2);
}