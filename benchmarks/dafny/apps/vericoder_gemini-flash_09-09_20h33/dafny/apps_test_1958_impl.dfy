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
function computeTotalPaymentIterative(n: int, p: int, buyers: seq<string>): int
    requires 1 <= n <= 40
    requires 2 <= p <= 1000
    requires p % 2 == 0
    requires |buyers| == n
    requires forall i :: 0 <= i < |buyers| ==> buyers[i] == "half" || buyers[i] == "halfplus"
    ensures computeTotalPaymentIterative(n, p, buyers) >= 0
    ensures computeTotalPaymentIterative(n, p, buyers) == computeTotalPayment(buyers, p)
{
    var totalPayment := 0;
    var currentApples := 0;
    for i := n - 1 downto 0
        invariant -1 <= i < n
        invariant currentApples >= 0
        invariant totalPayment >= 0
        invariant currentApples == computeApplesInFuture(buyers, i + 1, 0)
        invariant totalPayment == computePaymentForPastBuyers(buyers, p, i + 1, currentApples)
    {
        var newApples := if buyers[i] == "halfplus" then
                            currentApples * 2 + 1
                         else
                            currentApples * 2;
        var payment := 0;
        if buyers[i] == "halfplus" then
            payment := (newApples / 2) * p;
        else
            payment := currentApples * p;
        
        totalPayment := totalPayment + payment;
        currentApples := newApples;
    }
    return totalPayment;
}

function computeApplesInFuture(buyers: seq<string>, currentIndex: int, currentApples: int): int
    requires currentIndex >= 0
    requires currentApples >= 0
    requires forall i :: 0 <= i < |buyers| ==> buyers[i] == "half" || buyers[i] == "halfplus"
    // This function calculates how many apples are 'passed down' from buyers prior to `currentIndex`.
    // It is equivalent to reversing the perspective of `computePaymentBackward`.
    decreases |buyers| - currentIndex
{
    if currentIndex >= |buyers| then
        currentApples
    else
        var nextApples := if buyers[currentIndex] == "halfplus" then
                              currentApples * 2 + 1
                          else
                              currentApples * 2;
        computeApplesInFuture(buyers, currentIndex + 1, nextApples)
}

function computePaymentForPastBuyers(buyers: seq<string>, p: int, currentIndex: int, currentApplesSum: int): int
    requires p >= 0
    requires p % 2 == 0
    requires currentIndex >= 0
    requires currentApplesSum >= 0
    requires forall i :: 0 <= i < |buyers| ==> buyers[i] == "half" || buyers[i] == "halfplus"
    // This function calculates the total payment from `currentIndex` onwards,
    // assuming `currentApplesSum` is the total apples required by buyers *before* `currentIndex`.
    // It aims to mirror the `totalPayment` accumulation in the iterative function.
    decreases |buyers| - currentIndex
{
    if currentIndex >= |buyers| then 0
    else
        var nextApples := if buyers[currentIndex] == "halfplus" then
                              currentApplesSum * 2 + 1
                          else
                              currentApplesSum * 2;
        var payment := if buyers[currentIndex] == "halfplus" then
                           (nextApples / 2) * p
                       else
                           currentApplesSum * p;
        payment + computePaymentForPastBuyers(buyers, p, currentIndex + 1, nextApples)
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
  for i := n - 1 downto 0
    invariant -1 <= i < n
    invariant currentApples >= 0
    invariant totalPayment >= 0
    invariant currentApples == computeApplesInFuture(buyers, i + 1, 0)
    invariant totalPayment == computePaymentForPastBuyers(buyers, p, i + 1, 0)
    invariant totalPayment + computePaymentBackward(buyers, p, i, currentApples) == computeTotalPayment(buyers, p)
  {
      var newApples := if buyers[i] == "halfplus" then
                          currentApples * 2 + 1
                       else
                          currentApples * 2;
      var payment := 0;
      if buyers[i] == "halfplus" then
          payment := (newApples / 2) * p;
      else
          payment := currentApples * p;
      totalPayment := totalPayment + payment;
      currentApples := newApples;
  }
  return totalPayment;
}
// </vc-code>

