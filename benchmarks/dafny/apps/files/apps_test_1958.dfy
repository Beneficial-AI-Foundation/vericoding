Given n buyers and cost p per apple, determine total money seller should receive.
Each buyer purchased exactly half the apples available at their turn.
If apples were odd, buyer received additional half apple as gift.
Seller started with some positive number of apples and ended with zero apples.

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

method solve(n: int, p: int, buyers: seq<string>) returns (result: int)
    requires ValidInput(n, p, buyers)
    ensures result >= 0
    ensures result == computeTotalPayment(buyers, p)
{
    var num := 0;
    var num2 := 0;
    var i := n - 1;

    while i >= 0
        invariant -1 <= i < n
        invariant num >= 0
        invariant num2 >= 0
        invariant num2 + computePaymentBackward(buyers, p, i, num) == computeTotalPayment(buyers, p)
    {
        if buyers[i] == "halfplus" {
            num := num * 2 + 1;
            num2 := num2 + (num / 2) * p;
        } else {
            num2 := num2 + num * p;
            num := num * 2;
        }
        i := i - 1;
    }

    result := num2;
}
