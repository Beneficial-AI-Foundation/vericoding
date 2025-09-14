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

// </vc-helpers>

// <vc-spec>
method solve(n: int, p: int, buyers: seq<string>) returns (result: int)
    requires ValidInput(n, p, buyers)
    ensures result >= 0
    ensures result == computeTotalPayment(buyers, p)
// </vc-spec>
// <vc-code>
{
  var i := n - 1;
  var apples: int := 0;
  var total_payment: int := 0;

  while i >= 0
    decreases i
    invariant -1 <= i < n
    invariant |buyers| == n
    invariant p % 2 == 0
    invariant forall k :: 0 <= k < |buyers| ==> buyers[k] == "half" || buyers[k] == "halfplus"
    invariant apples >= 0
    invariant total_payment >= 0
    invariant total_payment + computePaymentBackward(buyers, p, i, apples) == computeTotalPayment(buyers, p)
  {
    var new_apples := if buyers[i] == "halfplus" then 
                        apples * 2 + 1
                      else 
                        apples * 2;
    var payment := if buyers[i] == "halfplus" then 
                      (new_apples / 2) * p
                   else 
                      apples * p;

    total_payment := total_payment + payment;
    apples := new_apples;
    i := i - 1;
  }
  result := total_payment;
}
// </vc-code>

