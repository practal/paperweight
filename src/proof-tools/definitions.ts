import { Term } from "../kernel/index.js";
import { Thm, S, subst, thm } from "../workbench.js";
import { modusPonens } from "../theories/Implication.theory.js";
import { equalsSym, substEquals } from "../theories/Equality.theory.js";

type Instantiation = (string | Term)[];
type SafeDefinitionOptions = {
    rename: Instantiation,
    instantiate?: Instantiation,
    equalityTemplate?: string | Term,
    symmetric?: boolean,
};

function instantiate(theorem: Thm, varsAndTerms: Instantiation = []): Thm {
    return varsAndTerms.length === 0 ? theorem : subst(S(...varsAndTerms), theorem);
}

export function rewriteWithEquality(thmToRewrite: Thm, equality: Thm, outerTemplate: string | Term): Thm {
    return modusPonens(subst(S("A", outerTemplate), substEquals(equality)), thmToRewrite);
}

export function transportAcrossEquality(equality: Thm, equalityTemplate: string | Term = "t. t"): Thm {
    return subst(S("A", equalityTemplate), substEquals(equality));
}

export function transportProvenEquality(equality: Thm, equalityTemplate: string | Term = "t. t"): Thm {
    return transportAcrossEquality(equality, equalityTemplate);
}

export function equalityAsImplication(equality: Thm): Thm {
    return transportProvenEquality(equality, "t. t");
}

export function definitionEquality(definitionLabel: string, varsAndTerms: Instantiation = []): Thm {
    return instantiate(thm(definitionLabel), varsAndTerms);
}

export function definitionEqualitySym(definitionLabel: string, varsAndTerms: Instantiation = []): Thm {
    return equalsSym(definitionEquality(definitionLabel, varsAndTerms));
}

export function unfoldDefinition(
    thmToRewrite: Thm,
    definitionLabel: string,
    outerTemplate: string | Term,
    varsAndTerms: Instantiation = [],
): Thm {
    return rewriteWithEquality(thmToRewrite, definitionEquality(definitionLabel, varsAndTerms), outerTemplate);
}

export function foldDefinition(
    thmToRewrite: Thm,
    definitionLabel: string,
    outerTemplate: string | Term,
    varsAndTerms: Instantiation = [],
): Thm {
    return rewriteWithEquality(thmToRewrite, definitionEqualitySym(definitionLabel, varsAndTerms), outerTemplate);
}

export function transportDefinition(
    definitionLabel: string,
    options: {
        varsAndTerms?: Instantiation,
        equalityTemplate?: string | Term,
        symmetric?: boolean,
    } = {},
): Thm {
    const equality = options.symmetric
        ? definitionEqualitySym(definitionLabel, options.varsAndTerms)
        : definitionEquality(definitionLabel, options.varsAndTerms);
    return transportAcrossEquality(equality, options.equalityTemplate);
}

// Safe pattern for formulas like A[x]:
// 1. rename schematic variables in the definition theorem
// 2. derive the transport theorem
// 3. instantiate the renamed symbols afterward
export function transportDefinitionSafe(
    definitionLabel: string,
    options: SafeDefinitionOptions,
): Thm {
    const renamed = instantiate(thm(definitionLabel), options.rename);
    const equality = options.symmetric ? equalsSym(renamed) : renamed;
    const transport = transportAcrossEquality(equality, options.equalityTemplate);
    return instantiate(transport, options.instantiate);
}

export function transportDefinitionRenamed(
    definitionLabel: string,
    options: SafeDefinitionOptions,
): Thm {
    return transportDefinitionSafe(definitionLabel, options);
}

export function rewriteDefinitionSafe(
    thmToRewrite: Thm,
    definitionLabel: string,
    outerTemplate: string | Term,
    options: Omit<SafeDefinitionOptions, "equalityTemplate" | "symmetric"> & {
        symmetric?: boolean,
    },
): Thm {
    return modusPonens(transportDefinitionSafe(definitionLabel, {
        ...options,
        equalityTemplate: outerTemplate,
    }), thmToRewrite);
}

export function unfoldDefinitionSafe(
    thmToRewrite: Thm,
    definitionLabel: string,
    outerTemplate: string | Term,
    options: Omit<SafeDefinitionOptions, "equalityTemplate" | "symmetric">,
): Thm {
    return rewriteDefinitionSafe(thmToRewrite, definitionLabel, outerTemplate, options);
}

export function foldDefinitionSafe(
    thmToRewrite: Thm,
    definitionLabel: string,
    outerTemplate: string | Term,
    options: Omit<SafeDefinitionOptions, "equalityTemplate" | "symmetric">,
): Thm {
    return rewriteDefinitionSafe(thmToRewrite, definitionLabel, outerTemplate, {
        ...options,
        symmetric: true,
    });
}
