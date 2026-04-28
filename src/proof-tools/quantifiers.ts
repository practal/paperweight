import { Thm, bind, infer, thm, subst, S } from "../workbench.js";

export function bindPremise(theorem: Thm, instancePremise: string, templatePremise: string): Thm {
    return bind(instancePremise, templatePremise, theorem);
}

export const generalizePremise = bindPremise;

export function forAllIntroOf(bodyTemplate: string, theorem: Thm): Thm {
    return infer(subst(S("A", bodyTemplate), thm("for-all_intro")), theorem);
}

export function forAllIntroFrom(
    theorem: Thm,
    bodyTemplate: string,
    instancePremise?: string,
    templatePremise?: string,
): Thm {
    const prepared = instancePremise !== undefined && templatePremise !== undefined
        ? bindPremise(theorem, instancePremise, templatePremise)
        : theorem;
    return forAllIntroOf(bodyTemplate, prepared);
}
