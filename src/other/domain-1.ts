export const DOMAIN = [0, 1, 2];

export type Domain = number;

export function checkDomain(a : Domain) {
    if (a === 0 || a === 1 || a === 2) return;
    throw new Error("Value is not in domain: " + a);
}

export function isTrue(a : Domain) : boolean {
    checkDomain(a);
    return a === 2;
}

export function meet(a : Domain, b : Domain) : Domain {
    checkDomain(a);
    checkDomain(b);
    return Math.min(a, b);
}

export function leq(a : Domain, b : Domain) : boolean {
    checkDomain(a);
    checkDomain(b);
    return a <= b;
}
