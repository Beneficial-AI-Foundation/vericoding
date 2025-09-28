// <vc-preamble>
// Power function for real numbers with natural exponent
function Power(base: real, exp: nat): real
{
    if exp == 0 then 1.0
    else base * Power(base, exp - 1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method PolyVander2D(x: seq<real>, y: seq<real>, xDeg: nat, yDeg: nat) 
    returns (result: seq<seq<real>>)
    requires |x| == |y|
    requires |x| > 0
    ensures |result| == |x|
    ensures forall k :: 0 <= k < |result| ==> |result[k]| == (xDeg + 1) * (yDeg + 1)
    ensures forall k :: 0 <= k < |result| ==>
        forall i :: 0 <= i <= xDeg ==>
            forall j :: 0 <= j <= yDeg ==>
                var colIdx := (yDeg + 1) * i + j;
                colIdx < |result[k]| && 
                result[k][colIdx] == Power(x[k], i) * Power(y[k], j)
// </vc-spec>
// <vc-code>
{
  result := [];
  var k := 0;
  while k < |x|
    invariant 0 <= k <= |x|
    invariant |result| == k
    invariant forall idx :: 0 <= idx < k ==> |result[idx]| == (xDeg + 1) * (yDeg + 1)
    invariant forall idx :: 0 <= idx < k ==>
        forall i :: 0 <= i <= xDeg ==>
            forall j :: 0 <= j <= yDeg ==>
                var colIdx := (yDeg + 1) * i + j;
                colIdx < |result[idx]| && 
                result[idx][colIdx] == Power(x[idx], i) * Power(y[idx], j)
  {
    var row := [];
    var i := 0;
    while i <= xDeg
      invariant 0 <= i <= xDeg + 1
      invariant |row| == i * (yDeg + 1)
      invariant forall ii :: 0 <= ii < i ==>
          forall j :: 0 <= j <= yDeg ==>
              var colIdx := (yDeg + 1) * ii + j;
              colIdx < |row| && 
              row[colIdx] == Power(x[k], ii) * Power(y[k], j)
    {
      var j := 0;
      while j <= yDeg
        invariant 0 <= j <= yDeg + 1
        invariant |row| == i * (yDeg + 1) + j
        invariant forall ii :: 0 <= ii < i ==>
            forall jj :: 0 <= jj <= yDeg ==>
                var colIdx := (yDeg + 1) * ii + jj;
                colIdx < |row| && 
                row[colIdx] == Power(x[k], ii) * Power(y[k], jj)
        invariant forall jj :: 0 <= jj < j ==>
            var colIdx := (yDeg + 1) * i + jj;
            colIdx < |row| && 
            row[colIdx] == Power(x[k], i) * Power(y[k], jj)
      {
        var val := Power(x[k], i) * Power(y[k], j);
        row := row + [val];
        j := j + 1;
      }
      i := i + 1;
    }
    result := result + [row];
    k := k + 1;
  }
}
// </vc-code>
