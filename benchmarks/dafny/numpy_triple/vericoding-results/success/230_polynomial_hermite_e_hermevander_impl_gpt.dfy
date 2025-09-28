// <vc-preamble>
// Ghost function to compute HermiteE polynomial values using the recurrence relation
ghost function HermiteE(n: nat, x: real): real
  decreases n
{
  if n == 0 then 1.0
  else if n == 1 then x
  else x * HermiteE(n-1, x) - (n-1) as real * HermiteE(n-2, x)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): replaced sequence comprehensions with recursive ghost builders to avoid parse errors */
ghost function BuildRow(xv: real, deg: nat): seq<real>
  ensures |BuildRow(xv, deg)| == deg + 1
  ensures forall j: nat :: j < deg + 1 ==> BuildRow(xv, deg)[j] == HermiteE(j, xv)
  decreases deg
{
  if deg == 0 then [1.0]
  else BuildRow(xv, deg - 1) + [HermiteE(deg, xv)]
}

/* helper modified by LLM (iteration 3): recursive ghost matrix builder using BuildRow */
ghost function BuildMatrix(x: seq<real>, deg: nat): seq<seq<real>>
  ensures |BuildMatrix(x, deg)| == |x|
  ensures forall i: nat :: i < |x| ==> |BuildMatrix(x, deg)[i]| == deg + 1
  ensures forall i: nat, j: nat :: i < |x| && j < deg + 1 ==> BuildMatrix(x, deg)[i][j] == HermiteE(j, x[i])
  decreases |x|
{
  if |x| == 0 then []
  else BuildMatrix(x[..|x|-1], deg) + [BuildRow(x[|x|-1], deg)]
}
// </vc-helpers>

// <vc-spec>
method HermeVander(x: seq<real>, deg: nat) returns (result: seq<seq<real>>)
  requires |x| >= 0
  ensures |result| == |x|
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == deg + 1
  // Each element of the result matrix equals the corresponding HermiteE polynomial
  ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==>
    result[i][j] == HermiteE(j, x[i])
  // First column is all ones (He_0(x) = 1)
  ensures forall i :: 0 <= i < |result| ==> result[i][0] == 1.0
  // Second column equals x when deg > 0 (He_1(x) = x)
  ensures deg > 0 ==> forall i :: 0 <= i < |result| ==> result[i][1] == x[i]
  // Subsequent columns follow the HermiteE recurrence relation
  ensures forall i, j :: 0 <= i < |result| && 2 <= j <= deg ==>
    result[i][j] == x[i] * result[i][j-1] - (j-1) as real * result[i][j-2]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): iterative construction of HermiteE Vandermonde matrix without assumes; handle deg cases and maintain invariants */
  var res: seq<seq<real>> := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |res| == i
    invariant forall ii :: 0 <= ii < |res| ==> |res[ii]| == deg + 1
    invariant forall ii, j :: 0 <= ii < |res| && 0 <= j < |res[ii]| ==> res[ii][j] == HermiteE(j as nat, x[ii])
    decreases |x| - i
  {
    var row: seq<real>;
    if deg == 0 {
      row := [1.0];
      assert forall k :: 0 <= k < |row| ==> row[k] == HermiteE(k as nat, x[i]);
    } else {
      row := [1.0, x[i]];
      if deg >= 2 {
        var j := 2;
        while j <= deg
          invariant 2 <= j
          invariant j <= deg + 1
          invariant |row| == j
          invariant forall k :: 0 <= k < |row| ==> row[k] == HermiteE(k as nat, x[i])
          decreases deg - j
        {
          row := row + [x[i] * row[j - 1] - (j - 1) as real * row[j - 2]];
          j := j + 1;
        }
      } else {
        assert forall k :: 0 <= k < |row| ==> row[k] == HermiteE(k as nat, x[i]);
      }
    }
    res := res + [row];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
