Two players play a game on an array of integers, alternating turns.
First player removes subsegments with odd sum, second player removes subsegments with even sum.
After removal, remaining parts are concatenated. Player who cannot move loses.
Determine the winner assuming optimal play.

predicate AllEven(a: seq<int>)
{
    forall i :: 0 <= i < |a| ==> a[i] % 2 == 0
}

predicate HasOdd(a: seq<int>)
{
    exists i :: 0 <= i < |a| && a[i] % 2 == 1
}

method solve(a: seq<int>) returns (result: string)
    ensures result == "Second" <==> AllEven(a)
    ensures result == "First" <==> HasOdd(a)
    ensures result == "First" || result == "Second"
{
    var oddCount := 0;
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant oddCount >= 0
        invariant oddCount == 0 <==> (forall j :: 0 <= j < i ==> a[j] % 2 == 0)
        invariant oddCount > 0 <==> (exists j :: 0 <= j < i && a[j] % 2 == 1)
    {
        if a[i] % 2 == 1 {
            oddCount := oddCount + 1;
        }
        i := i + 1;
    }

    if oddCount == 0 {
        result := "Second";
    } else {
        result := "First";
    }
}
