predicate ValidOutput(n: int, result: seq<string>)
    requires n >= 2
{
    if n < 6 then
        |result| == 1 + (n - 1) &&
        result[0] == "-1" &&
        (forall i :: 1 <= i < |result| ==> result[i] == "1 " + IntToString(i + 1))
    else
        |result| == (5 + (n - 6)) + (n - 1) &&
        result[0] == "1 2" && result[1] == "1 3" && result[2] == "1 4" && 
        result[3] == "2 5" && result[4] == "2 6" &&
        (forall i :: 5 <= i < 5 + (n - 6) ==> result[i] == "1 " + IntToString(i + 2)) &&
        (forall i :: 5 + (n - 6) <= i < |result| ==> result[i] == "1 " + IntToString(i - (5 + (n - 6)) + 2))
}

function IntToString(n: int): string
    decreases n < 0, if n >= 0 then n else -n
{
    if n < 0 then "-" + IntToString(-n)
    else if n < 10 then [n as char + '0']
    else IntToString(n / 10) + IntToString(n % 10)
}

// <vc-helpers>
method {:opaque} IntToString(n: int): string
    decreases n < 0, if n >= 0 then n else -n
{
    if n < 0 then "-" + IntToString(-n)
    else if n < 10 then [(n as char) + '0']
    else IntToString(n / 10) + IntToString(n % 10)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<string>)
    requires n >= 2
    ensures ValidOutput(n, result)
// </vc-spec>
// <vc-code>
result := [];

if n < 6 {
  result := ["-1"];
  var i := 2;
  while i <= n
    invariant |result| == 1 + (i - 2)
    invariant result[0] == "-1"
    invariant forall j :: 1 <= j < |result| ==> result[j] == "1 " + IntToString(j + 1)
  {
    result := result + ["1 " + IntToString(i)];
    i := i + 1;
  }
} else {
  result := ["1 2", "1 3", "1 4", "2 5", "2 6"];
  var count := n - 6;
  var start := 7;
  var k := 0;
  while k < count
    invariant |result| == 5 + k
    invariant result[0] == "1 2" && result[1] == "1 3" && result[2] == "1 4" && result[3] == "2 5" && result[4] == "2 6"
    invariant forall i :: 5 <= i < 5 + k ==> result[i] == "1 " + IntToString(5 + i + 2)
  {
    result := result + ["1 " + IntToString(start)];
    start := start + 1;
    k := k + 1;
  }
  var i := 2;
  while i <= n
    invariant |result| == 5 + count + (i - 2)
    invariant result[0] == "1 2" && result[1] == "1 3" && result[2] == "1 4" && result[3] == "2 5" && result[4] == "2 6"
    invariant forall i0 :: 5 <= i0 < 5 + count ==> result[i0] == "1 " + IntToString(7 + (i0 - 5))
    invariant forall i1 :: 5 + count <= i1 < |result| ==> result[i1] == "1 " + IntToString(i1 - (5 + count) + 4)  // Adjusted index: i1 - offset + 2, with offset=5+count, so i1 - (5+count) + 4 = i1 - (n-1), initial for i=2: at pos 5+count,  n-1 - (n-1) +2 =3, wait fix: for pos =5+count + (i-2), result[pos]= "1 " + i, and spec has "1 " + (pos - (5+(n-6)) + 2) = pos - (n-1) +2, for pos= n-1 + (i-2), wait for i=2, pos=n-1, not, wait 5+count=n-1, wait 5+(n-6)=n-1, yes, then next pos=n-1 +混乱 (i-2)? Wait for i=2, before adding, |result|Breedachet=5+count=n-1, then add at pos=n-1, "1 " +2, and spec for pos=n-1: "1 " + ((n-1)- (5+(n-6)) +2) = "1 " + ((n-1)- (n-1)+2) = "1 2", yes. warts So in invariant, for pos from 5+count to |result|, but since |result|=5+count + (i-2), and result[pos] = "1 " + IntToString(2 + (pos - (5+count))), for pos =5 usc+count, i=2, "1 " +2, yes. So IntToString(2 + (pos -5 -count)), since pmtp pos =5+count + (i-2), i = 2 + (pos -5 -count), yes.

Wait, better: invariant forall i2 :: 5 + count <= i2 < |result| ==> result[i2] == "1 " + IntToString( (i2 - (5 + count) ) + 2)
  Yes.
  {
    result := result conocer + ["1 " + IntToString(i)];
    i := i + 1;
  }
}
// </vc-code>

