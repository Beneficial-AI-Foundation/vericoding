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
lemma ComputePaymentBackwardNonNegative(buyers: seq<string>, p: int, currentIndex: int, currentApples: int)
    requires p >= 0
    requires p % 2 == 0
    requires -1 <= currentIndex < |buyers|
    requires currentApples >= 0
    requires forall i :: 0 <= i < |buyers| ==> buyers[i] == "half" || buyers[i] == "halfplus"
    ensures computePaymentBackward(buyers, p, currentIndex, currentApples) >= 0
{
    if currentIndex < 0 {
        // Base case: trivially true
    } else {
        var newApples := if buyers[currentIndex] == "halfplus" then 
                            currentApples * 2 + 1
                         else 
                            currentApples * 2;
        var payment := if buyers[currentIndex] == "halfplus" then 
                          (newApples / 2) * p
                       else 
                          currentApples * p;
        
        // Recursive call lemma
        ComputePaymentBackwardNonNegative(buyers, p, currentIndex - 1, newApples);
    }
}

function iterativeComputePayment(buyers: seq<string>, p: int): int
    requires p >= 0
    requires p % 2 == 0
    requires forall i :: 0 <= i < |buyers| ==> buyers[i] == "half" || buyers[i] == "halfplus"
    ensures iterativeComputePayment(buyers, p) >= 0
{
    var totalPayment := 0;
    var currentApples := 0;
    iterativeHelper(buyers, p, |buyers| - 1, currentApples, totalPayment)
}

function iterativeHelper(buyers: seq<string>, p: int, index: int, currentApples: int, totalPayment: int): int
    requires p >= 0
    requires p % 2 == 0
    requires -1 <= index < |buyers|
    requires currentApples >= 0
    requires totalPayment >= 0
    requires forall i :: 0 <= i < |buyers| ==> buyers[i] == "half" || buyers[i] == "halfplus"
    ensures iterativeHelper(buyers, p, index, currentApples, totalPayment) >= 0
{
    if index < 0 then totalPayment
    else
        var newApples := if buyers[index] == "halfplus" then 
                            currentApples * 2 + 1
                         else 
                            currentApples * 2;
        var payment := if buyers[index] == "halfplus" then 
                          (newApples / 2) * p
                       else 
                          currentApples * p;
        iterativeHelper(buyers, p, index - 1, newApples, totalPayment + payment)
}

lemma IterativeEqualsRecursive(buyers: seq<string>, p: int)
    requires p >= 0
    requires p % 2 == 0
    requires forall i :: 0 <= i < |buyers| ==> buyers[i] == "half" || buyers[i] == "halfplus"
    ensures iterativeComputePayment(buyers, p) == computeTotalPayment(buyers, p)
{
    IterativeEqualsRecursiveHelper(buyers, p, |buyers| - 1, 0, 0);
}

lemma IterativeEqualsRecursiveHelper(buyers: seq<string>, p: int, index: int, currentApples: int, totalPayment: int)
    requires p >= 0
    requires p % 2 == 0
    requires -1 <= index < |buyers|
    requires currentApples >= 0
    requires totalPayment >= 0
    requires forall i :: 0 <= i < |buyers| ==> buyers[i] == "half" || buyers[i] == "halfplus"
    ensures iterativeHelper(buyers, p, index, currentApples, totalPayment) == 
            totalPayment + computePaymentBackward(buyers, p, index, currentApples)
{
    if index < 0 {
        // Base case
    } else {
        var newApples := if buyers[index] == "halfplus" then 
                            currentApples * 2 + 1
                         else 
                            currentApples * 2;
        var payment := if buyers[index] == "halfplus" then 
                          (newApples / 2) * p
                       else 
                          currentApples * p;
        IterativeEqualsRecursiveHelper(buyers, p, index - 1, newApples, totalPayment + payment);
    }
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
    result := 0;
    var currentApples := 0;
    var i := n - 1;
    
    while i >= 0
        invariant -1 <= i < n
        invariant currentApples >= 0
        invariant result >= 0
        invariant result + computePaymentBackward(buyers, p, i, currentApples) == computeTotalPayment(buyers, p)
    {
        var newApples := if buyers[i] == "halfplus" then 
                            currentApples * 2 + 1
                         else 
                            currentApples * 2;
        var payment := if buyers[i] == "halfplus" then 
                          (newApples / 2) * p
                       else 
                          currentApples * p;
        
        result := result + payment;
        currentApples := newApples;
        i := i - 1;
        
        ComputePaymentBackwardNonNegative(buyers, p, i, currentApples);
    }
}
// </vc-code>

