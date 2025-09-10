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
    var totalPaymentLocal := 0;
    var currentApplesLocal := 0;
    for i := n - 1 downto 0
        invariant -1 <= i < n
        invariant currentApplesLocal >= 0
        invariant totalPaymentLocal >= 0
        // The invariants should relate to the original problem functions.
        // It's helpful to realize that `currentApplesLocal` at index `i` (looking backward)
        // corresponds to the `currentApples` parameter passed to `computePaymentBackward`
        // when computing the payment for index `i-1`.
        // And `totalPaymentLocal` accumulates payments from `i+1` to `n-1`.
        // The relationship to `computePaymentBackward` and `computeTotalPayment` is:
        // `totalPaymentLocal + computePaymentBackward(buyers, p, i, currentApplesLocal)` should be constant.
        // And at the start, `i = n-1`, `totalPaymentLocal = 0`, `currentApplesLocal = 0`,
        // so `computePaymentBackward(buyers, p, n-1, 0)` is the target value.
        invariant totalPaymentLocal + computePaymentBackward(buyers, p, i, currentApplesLocal) == computeTotalPayment(buyers, p)
    {
        var newApples := if buyers[i] == "halfplus" then
                            currentApplesLocal * 2 + 1
                         else
                            currentApplesLocal * 2;
        var payment := 0;
        if buyers[i] == "halfplus" then
            payment := (newApples / 2) * p;
        else
            payment := currentApplesLocal * p;
        
        totalPaymentLocal := totalPaymentLocal + payment;
        currentApplesLocal := newApples;
    }
    return totalPaymentLocal;
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
    // The invariant `totalPayment == computePaymentForPastBuyers(buyers, p, i + 1, 0)` is not quite right.
    // `computePaymentForPastBuyers` starts with `currentApplesSum` being the apples for the current segment,
    // not necessarily 0.
    // The key invariant that links `totalPayment` and `currentApples` in the loop
    // to the recursive definition `computeTotalPayment` is:
    // `totalPayment + computePaymentBackward(buyers, p, i, currentApples) == computeTotalPayment(buyers, p)`.
    // Let's verify this.
    // Base case: i = n-1. Loop starts with totalPayment = 0, currentApples = 0.
    // totalPayment + computePaymentBackward(buyers, p, n-1, 0) == computePaymentBackward(buyers, p, n-1, 0) == computeTotalPayment(buyers, p) (by definition of computeTotalPayment).
    // Induction step:
    // Assume `totalPayment_old + computePaymentBackward(buyers, p, i_old, currentApples_old) == computeTotalPayment(buyers, p)`
    // And `i = i_old - 1`.
    // We update:
    // `newApples = if buyers[i_old] == "halfplus" then currentApples_old * 2 + 1 else currentApples_old * 2`
    // `payment = if buyers[i_old] == "halfplus" then (newApples/2) * p else currentApples_old * p`
    // `totalPayment = totalPayment_old + payment`
    // `currentApples = newApples`
    // From `computePaymentBackward` definition:
    // `computePaymentBackward(buyers, p, i_old, currentApples_old) == payment_for_i_old + computePaymentBackward(buyers, p, i_old - 1, newApples)`
    // where `payment_for_i_old` is the payment at `i_old` given `currentApples_old`.
    // Note that the implementation's `payment` variable is exactly this `payment_for_i_old`,
    // and `newApples` is passed as `currentApples_old` to the recursive call.
    // So, `computePaymentBackward(buyers, p, i_old, currentApples_old) == payment + computePaymentBackward(buyers, p, i, currentApples)`.
    // Substitute into the inductive hypothesis:
    // `totalPayment_old + (payment + computePaymentBackward(buyers, p, i, currentApples)) == computeTotalPayment(buyers, p)`
    // `(totalPayment_old + payment) + computePaymentBackward(buyers, p, i, currentApples) == computeTotalPayment(buyers, p)`
    // `totalPayment + computePaymentBackward(buyers, p, i, currentApples) == computeTotalPayment(buyers, p)`
    // This holds.

    // Also, the relation between `currentApples` and `computeApplesInFuture` is the following:
    // `currentApples` in the loop at iteration `i` (for `buyers[i]`) corresponds to the total number
    // of apples needed by buyers whose indices are `i+1` to `n-1` (after `buyers[i]` buys).
    // `computeApplesInFuture(buyers, i + 1, 0)` calculates the total apples needed for buyers from `i+1` to `n-1`,
    // given that the initial `currentApples` passed to it is 0. This matches.
    invariant currentApples == computeApplesInFuture(buyers, i + 1, 0)
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
          payment := currentApples * p; // This assumes currentApples is the total before the current buyer buys.
                                        // Which is true, currentApples is the total "passed down" from future buyers.
      totalPayment := totalPayment + payment;
      currentApples := newApples;
  }
  return totalPayment;
}
// </vc-code>

