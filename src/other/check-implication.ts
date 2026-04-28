import { Domain, DOMAIN, meet, leq, isTrue, checkDomain} from "./domain-2.js";

type Implication = (a : Domain, b : Domain) => Domain

function checkMP(implies : Implication) : boolean {
    for (const a of DOMAIN) {
        for (const b of DOMAIN) {
            const top = meet(implies(a, b), a);
            const bottom = b;
            if (!leq(top, bottom)) {
                console.log("MP: does not hold for A = " + a + ", B = " + b);
                return false;
            }
        }
    }
    return true;
}

function checkImplies1(implies : Implication) : boolean {
    for (const a of DOMAIN) {
        for (const b of DOMAIN) {
            const t = implies(a, implies(b, a));
            if (!isTrue(t)) {
                console.log("Implies1: does not hold for A = " + a + ", B = " + b);
                return false;
            }
        }
    }
    return true;
}

function checkImplies2(implies : Implication) : boolean {
    for (const a of DOMAIN) {
        for (const b of DOMAIN) {
            for (const c of DOMAIN) {
                const left = implies(a, implies(b, c));
                const right = implies(implies(a, b), implies(a, c));
                const t = implies(left, right);
                if (!isTrue(t)) {
                    console.log("Implies2: does not hold for A = " + a + ", B = " + b + ", C = " + c);
                    return false;
                }
            }
        }
    }
    return true;
}

function hasNaturalDeduction(implies : Implication) : boolean {
    for (const a of DOMAIN) {
        for (const b of DOMAIN) {
            for (const c of DOMAIN) {
                // if c, a / b holds, then c / implies(a, b) holds
                if (leq(meet(c, a), b) && !leq(c, implies(a, b))) {
                    return false;
                }
            }
        }
    }
    return true;
}

function checkImplication(implies : Implication) {
    if (!checkMP(implies)) return;
    if (!checkImplies1(implies)) return;
    if (!checkImplies2(implies)) return;
    console.log("has Natural Deduction: " + hasNaturalDeduction(implies));
    console.log("Implication checks out fine.");
}

function fromTable(values : Domain[][]) : Implication {
    return (a : Domain, b : Domain) => {
        checkDomain(a);
        checkDomain(b);
        return values[a][b];
    }
}

const HeytingImplication = fromTable([
    [2, 2, 2],
    [0, 2, 2],
    [0, 1, 2]
]);

const CustomImplication = fromTable([
    [2, 1, 2],
    [0, 2, 2],
    [0, 1, 2]
]);

const CustomImplication2 = fromTable([
    [2, 1, 2],
    [2, 2, 2],
    [0, 1, 2]
]);

checkImplication(CustomImplication2);