// <vc-preamble>
// Helper function to find minimum value in a sequence
function Min(data: seq<real>): real
  requires |data| > 0
{
  if |data| == 1 then data[0]
  else if data[0] <= Min(data[1..]) then data[0]
  else Min(data[1..])
}

// Helper function to find maximum value in a sequence  
function Max(data: seq<real>): real
  requires |data| > 0
{
  if |data| == 1 then data[0]
  else if data[0] >= Max(data[1..]) then data[0]
  else Max(data[1..])
}

// Helper predicate to check if sequence is monotonically increasing
predicate IsMonotonicallyIncreasing(edges: seq<real>)
{
  forall i :: 0 <= i < |edges| - 1 ==> edges[i] < edges[i + 1]
}

// Helper predicate to check if bins have equal width
predicate HasEqualWidthBins(edges: seq<real>)
  requires |edges| >= 2
{
  forall i, j :: 0 <= i < |edges| - 1 && 0 <= j < |edges| - 1 ==>
    edges[i + 1] - edges[i] == edges[j + 1] - edges[j]
}

// Helper predicate to check if all data falls within edge range
predicate DataWithinEdgeRange(data: seq<real>, edges: seq<real>)
  requires |data| > 0 && |edges| >= 2
{
  forall i :: 0 <= i < |data| ==>
    edges[0] <= data[i] <= edges[|edges| - 1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): lemma that Min(data) is a lower bound for all elements */
lemma MinLowerBound(data: seq<real>)
  requires |data| > 0
  ensures forall i :: 0 <= i < |data| ==> Min(data) <= data[i]
{
  if |data| == 1 {
  } else {
    MinLowerBound(data[1..]);
    forall i | 0 <= i < |data|
      ensures Min(data) <= data[i]
    {
      if i == 0 {
        if data[0] <= Min(data[1..]) {
          assert Min(data) == data[0];
          assert Min(data) <= data[0];
        } else {
          assert Min(data) == Min(data[1..]);
          assert Min(data) <= data[0];
        }
      } else {
        var k := i - 1;
        assert 0 <= k;
        assert k < |data[1..]|;
        assert Min(data[1..]) <= data[1..][k];
        assert data[1..][k] == data[i];
        if data[0] <= Min(data[1..]) {
          assert Min(data) == data[0];
          assert data[0] <= Min(data[1..]);
          assert Min(data) <= data[i];
        } else {
          assert Min(data) == Min(data[1..]);
          assert Min(data) <= data[i];
        }
      }
    }
  }
}

/* helper modified by LLM (iteration 4): lemma that Max(data) is an upper bound for all elements */
lemma MaxUpperBound(data: seq<real>)
  requires |data| > 0
  ensures forall i :: 0 <= i < |data| ==> data[i] <= Max(data)
{
  if |data| == 1 {
  } else {
    MaxUpperBound(data[1..]);
    forall i | 0 <= i < |data|
      ensures data[i] <= Max(data)
    {
      if i == 0 {
        if data[0] >= Max(data[1..]) {
          assert Max(data) == data[0];
          assert data[0] <= Max(data);
        } else {
          assert Max(data) == Max(data[1..]);
          assert data[0] <= Max(data);
        }
      } else {
        var k := i - 1;
        assert 0 <= k;
        assert k < |data[1..]|;
        assert data[1..][k] <= Max(data[1..]);
        assert data[1..][k] == data[i];
        if data[0] >= Max(data[1..]) {
          assert Max(data) == data[0];
          assert data[i] <= Max(data[1..]);
          assert data[i] <= Max(data);
        } else {
          assert Max(data) == Max(data[1..]);
          assert data[i] <= Max(data);
        }
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method HistogramBinEdges(data: seq<real>, numBins: nat) returns (edges: seq<real>)
  // Input data must be non-empty and number of bins must be positive
  requires |data| > 0
  requires numBins > 0
  
  // Output has correct length: num_bins + 1 edges
  ensures |edges| == numBins + 1
  
  // Edges are monotonically increasing (strictly ordered)
  ensures IsMonotonicallyIncreasing(edges)
  
  // First edge is at or below minimum data value
  ensures edges[0] <= Min(data)
  
  // Last edge is at or above maximum data value  
  ensures edges[|edges| - 1] >= Max(data)
  
  // Bins have equal width (equal spacing between consecutive edges)
  ensures HasEqualWidthBins(edges)
  
  // All data values fall within the range of the edges
  ensures DataWithinEdgeRange(data, edges)
  
  // The bin width is consistent and positive
  ensures numBins > 0 ==> edges[1] - edges[0] > 0.0
  
  // The total range covered by edges spans at least the data range
  ensures edges[|edges| - 1] - edges[0] >= Max(data) - Min(data)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): construct equal-width edges covering data range and fix real coercions */
  MinLowerBound(data);
  MaxUpperBound(data);

  var L := Min(data);
  var m := Max(data);
  var n := numBins;
  var nR := n as real;
  assert nR > 0.0;

  assert Min(data) <= data[0];
  assert data[0] <= Max(data);
  assert L <= m;

  var U := m + nR; // ensure strictly positive width regardless of data range
  var w := (U - L) / nR;

  assert U - L == (m - L) + nR;
  assert m - L >= 0.0;
  assert U - L > 0.0;
  assert w > 0.0;

  var acc: seq<real> := [L];
  var i: nat := 0;
  while i < n
    invariant i <= n
    invariant |acc| == i + 1
    invariant acc[0] == L
    invariant forall k :: 0 <= k < |acc| ==> acc[k] == L + (k as real) * w
    decreases n - i
  {
    acc := acc + [acc[|acc| - 1] + w];
    i := i + 1;
  }
  edges := acc;

  assert |edges| == n + 1;

  // Edges are strictly increasing
  forall i | 0 <= i < |edges| - 1
    ensures edges[i] < edges[i + 1]
  {
    assert edges[i] == L + (i as real) * w;
    assert edges[i + 1] == L + ((i + 1) as real) * w;
    assert edges[i + 1] == edges[i] + w;
    assert w > 0.0;
  }

  // Equal width bins
  forall i, j | 0 <= i < |edges| - 1 && 0 <= j < |edges| - 1
    ensures edges[i + 1] - edges[i] == edges[j + 1] - edges[j]
  {
    assert edges[i] == L + (i as real) * w;
    assert edges[i + 1] == L + ((i + 1) as real) * w;
    assert edges[j] == L + (j as real) * w;
    assert edges[j + 1] == L + ((j + 1) as real) * w;
  }

  assert edges[0] == L;
  assert edges[|edges| - 1] == L + nR * w;
  assert edges[|edges| - 1] == U; // since w = (U - L)/nR and nR > 0
  assert m <= edges[|edges| - 1];

  // All data within [edges[0], edges[last]]
  forall k | 0 <= k < |data|
    ensures edges[0] <= data[k] <= edges[|edges| - 1]
  {
    assert Min(data) <= data[k];
    assert data[k] <= Max(data);
    assert edges[0] == L;
    assert edges[|edges| - 1] == U;
    assert m <= U;
  }

  // Total range covers data range
  assert edges[|edges| - 1] - edges[0] == U - L;
  assert U - L >= m - L;
}

// </vc-code>
