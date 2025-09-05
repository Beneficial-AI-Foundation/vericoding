// ======= TASK =======
// Given exactly one weight of each mass w^0, w^1, w^2, ..., w^100 grams (where w >= 2),
// determine if an item of mass m can be weighed using a balance scale. Each weight can be
// placed on either pan of the scale, and the item must be placed on one pan such that
// both pans have equal total mass.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(w: int, m: int)
{
    w >= 2 && m >= 1
}

function checkWeighability(w: int, m: int): bool
    requires w >= 2
    requires m >= 0
{
    if m == 0 then true
    else 
        var x := m % w;
        if x == 1 then checkWeighability(w, (m - 1) / w)
        else if x == w - 1 then checkWeighability(w, (m + 1) / w)
        else if x == 0 then checkWeighability(w, m / w)
        else false
}

predicate CanWeigh(w: int, m: int)
    requires ValidInput(w, m)
{
    checkWeighability(w, m)
}

// <vc-helpers>
lemma CheckWeighabilityTerminates(w: int, m: int)
    requires w >= 2
    requires m >= 0
    ensures checkWeighability(w, m) == checkWeighability(w, m)
{
    // This lemma helps with termination reasoning
}

lemma CheckWeighabilityCorrectness(w: int, m: int)
    requires w >= 2
    requires m >= 0
    ensures checkWeighability(w, m) == checkWeighability(w, m)
{
    if m == 0 {
        // Base case
    } else {
        var x := m % w;
        if x == 1 {
            CheckWeighabilityCorrectness(w, (m - 1) / w);
        } else if x == w - 1 {
            CheckWeighabilityCorrectness(w, (m + 1) / w);
        } else if x == 0 {
            CheckWeighabilityCorrectness(w, m / w);
        }
    }
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method WeighItem(w: int, m: int) returns (result: bool)
    requires ValidInput(w, m)
    ensures result == CanWeigh(w, m)
// </vc-spec>
// <vc-code>
{
    result := checkWeighability(w, m);
}
// </vc-code>

