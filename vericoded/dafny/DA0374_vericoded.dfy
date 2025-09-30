predicate ValidInput(n: int, p: int, buyers: seq<string>)
{
    1 <= n <= 40 &&
    2 <= p <= 1000 &&
    p % 2 == 0 &&
    |buyers| == n &&
    forall i :: 0 <= i < |buyers| ==> buyers[i] == "half" || buyers[i] == "halfplus"
}

function computeTotalPayment(buyers: seq<string>, p: int): int
    requires p >= 0
    requires p % 2 == 0
    requires forall i :: 0 <= i < |buyers| ==> buyers[i] == "half" || buyers[i] == "halfplus"
    ensures computeTotalPayment(buyers, p) >= 0
{
    computePaymentBackward(buyers, p, |buyers| - 1, 0)
}

function computePaymentBackward(buyers: seq<string>, p: int, currentIndex: int, currentApples: int): int
    requires p >= 0
    requires p % 2 == 0
    requires -1 <= currentIndex < |buyers|
    requires currentApples >= 0
    requires forall i :: 0 <= i < |buyers| ==> buyers[i] == "half" || buyers[i] == "halfplus"
    ensures computePaymentBackward(buyers, p, currentIndex, currentApples) >= 0
{
    if currentIndex < 0 then 0
    else
        var newApples := if buyers[currentIndex] == "halfplus" then 
                            currentApples * 2 + 1
                         else 
                            currentApples * 2;
        var payment := if buyers[currentIndex] == "halfplus" then 
                          (newApples / 2) * p
                       else 
                          currentApples * p;
        payment + computePaymentBackward(buyers, p, currentIndex - 1, newApples)
}

// <vc-helpers>
lemma ComputePaymentBackwardUnfolding(buyers: seq<string>, p: int, currentIndex: int, currentApples: int)
    requires p >= 0
    requires p % 2 == 0
    requires 0 <= currentIndex < |buyers|
    requires currentApples >= 0
    requires forall i :: 0 <= i < |buyers| ==> buyers[i] == "half" || buyers[i] == "halfplus"
    ensures computePaymentBackward(buyers, p, currentIndex, currentApples) ==
            (if buyers[currentIndex] == "halfplus" then
                var newApples := currentApples * 2 + 1;
                (newApples / 2) * p + computePaymentBackward(buyers, p, currentIndex - 1, newApples)
            else
                var newApples := currentApples * 2;
                currentApples * p + computePaymentBackward(buyers, p, currentIndex - 1, newApples))
{
    // This lemma just unfolds the definition once
}

lemma ComputeTotalPaymentIsBackwardFromEnd(buyers: seq<string>, p: int)
    requires p >= 0
    requires p % 2 == 0
    requires |buyers| > 0
    requires forall i :: 0 <= i < |buyers| ==> buyers[i] == "half" || buyers[i] == "halfplus"
    ensures computeTotalPayment(buyers, p) == computePaymentBackward(buyers, p, |buyers| - 1, 0)
{
    // By definition of computeTotalPayment
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, p: int, buyers: seq<string>) returns (result: int)
    requires ValidInput(n, p, buyers)
    ensures result >= 0
    ensures result == computeTotalPayment(buyers, p)
// </vc-spec>
// <vc-code>
{
    var totalPayment := 0;
    var currentApples := 0;
    var i := |buyers| - 1;
    
    while i >= 0
        invariant -1 <= i < |buyers|
        invariant currentApples >= 0
        invariant totalPayment >= 0
        invariant totalPayment == computePaymentBackward(buyers, p, |buyers| - 1, 0) - computePaymentBackward(buyers, p, i, currentApples)
    {
        if buyers[i] == "halfplus" {
            var newApples := currentApples * 2 + 1;
            var payment := (newApples / 2) * p;
            ComputePaymentBackwardUnfolding(buyers, p, i, currentApples);
            totalPayment := totalPayment + payment;
            currentApples := newApples;
        } else {
            var newApples := currentApples * 2;
            var payment := currentApples * p;
            ComputePaymentBackwardUnfolding(buyers, p, i, currentApples);
            totalPayment := totalPayment + payment;
            currentApples := newApples;
        }
        i := i - 1;
    }
    
    assert i == -1;
    assert currentApples >= 0;
    assert totalPayment == computePaymentBackward(buyers, p, |buyers| - 1, 0) - computePaymentBackward(buyers, p, -1, currentApples);
    assert computePaymentBackward(buyers, p, -1, currentApples) == 0;
    assert totalPayment == computePaymentBackward(buyers, p, |buyers| - 1, 0);
    
    result := totalPayment;
}
// </vc-code>

