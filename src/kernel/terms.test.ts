import { assertCrashT, Test } from "things";
import { defaultTerms } from "./default-terms.js";
import { displayTerm } from "./display.js";
import { AritySpec, emptySignature, ShapeSpec } from "./signature.js";

function firstSignatureTest() {
    const terms = defaultTerms;
    function vid(s : string) : string {
        return terms.mkId(s);
    }
    const x = vid("x");
    const y = terms.mkVarApp(vid("y"), []);
    const t = terms.mkVarApp(x, [y, y]);
    console.log(terms.display(t));
    let sig = emptySignature(terms.ids);
    sig = sig.declare([[terms.mkId("for-all"), {shape : [{name : vid("P"), binders: [vid("x"), vid("y")], variadic: vid("xs")}]}]]);
    assertCrashT(() => {
        sig.declare([[terms.mkId("for-all"), {shape : [{name : vid("P"), binders: [vid("x")], variadic:true}]}]]);    
    });
    sig = sig.declare([[terms.mkId("for-all"), {shape : [{name : vid("P"), binders: [vid("x")], variadic:false}]}]]);
    console.log("--- signature begin");
    for (const [id, absSigSpecs] of sig.allAbsSigSpecs()) {
        for (const absSigSpec of absSigSpecs) {
            console.log("spec '" + sig.display(absSigSpec) + "'");
        }
    }
    // declare for-all (x ... => P)
    console.log("--- signature end");
}

Test(() => {
    firstSignatureTest();
}, "firstSignatureTest");
