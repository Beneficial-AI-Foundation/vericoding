predicate ValidInput(n: int, a: int, b: int, mobs: seq<int>)
{
    n >= 0 && a > 0 && b > 0 && |mobs| == n &&
    forall i :: 0 <= i < n ==> mobs[i] >= 0
}

predicate ValidOutput(result: seq<string>, n: int)
{
    |result| == n &&
    forall i :: 0 <= i < n ==> result[i] in ["Vanya", "Vova", "Both"]
}

predicate CorrectResult(result: seq<string>, n: int, a: int, b: int, mobs: seq<int>)
    requires a > 0 && b > 0 && |mobs| == n
{
    ValidOutput(result, n) &&
    forall i :: 0 <= i < n ==> 
        var total := a + b;
        var k := if mobs[i] == 0 then 0 else mobs[i] % total;
        (result[i] == "Vanya" <==> determineWinner(k, a, b) == 0) &&
        (result[i] == "Vova" <==> determineWinner(k, a, b) == 1) &&
        (result[i] == "Both" <==> determineWinner(k, a, b) == 2)
}

// <vc-helpers>
function determineWinner(k: int, a: int, b: int): int
    requires a > 0 && b > 0 && 0 <= k < a + b
    ensures 0 <= result <= 2
{
    if k == 0 then 2
    else if k <= a then 0
    else 1
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, mobs: seq<int>) returns (result: seq<string>)
    requires ValidInput(n, a, b, mobs)
    ensures CorrectResult(result, n, a, b, mobs)
// </vc-spec>
// <vc-code>
{
  var arr := new string[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==>
      arr[j] in ["Vanya", "Vova", "Both"] &&
      (if mobs[j] == 0 then arr[j] == "Both"
       else if mobs[j] % (a + b) >= 1 && mobs[j] % (a + b) <= a then arr[j] == "Vanya"
       else arr[j] == "Vova")
  {
    var total := a + b;
    var k := if mobs[i] == 0 then 0 else mobs[i] % total;
    assert 0 <= k < total;
    if determineWinner(k, a, b) == 0 {
      arr[i] := "Vanya";
    } else if determineWinner(k, a, b) == 1 {
      arr[i] := "Vova";
    } else {
      arr[i] := "Both";
    }
    i := i + 1;
  }
  result := arr[..];
}
// </vc-code>

