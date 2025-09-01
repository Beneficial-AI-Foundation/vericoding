

// <vc-helpers>
function isMonotonicallyIncreasing(xs: seq<int>): bool
  reads xs
  ensures isMonotonicallyIncreasing(xs) <==> (forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j])
{
  forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]
}

function isMonotonicallyDecreasing(xs: seq<int>): bool
  reads xs
  ensures isMonotonicallyDecreasing(xs) <==> (forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j])
{
  forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j]
}
// </vc-helpers>

// <vc-spec>
method monotonic(xs: seq<int>) returns (result: bool)
  // pre-conditions-start
  requires |xs| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> (forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]) || (forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j])
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |xs| <= 1 then
    return true;
  else
    var increasing := true;
    var decreasing := true;

    for k := 0 to |xs| - 2
      invariant 0 <= k <= |xs| - 1
      invariant decreasing ==> (forall i, j :: 0 <= i < j <= k ==> xs[i] > xs[j])
      invariant increasing ==> (forall i, j :: 0 <= i < j <= k ==> xs[i] < xs[j])
      invariant k < |xs| ==> |xs| >= 1
    {
      if xs[k] >= xs[k+1] then
        increasing := false;
      if xs[k] <= xs[k+1] then
        decreasing := false;
    }

    return increasing || decreasing;
}
// </vc-code>

