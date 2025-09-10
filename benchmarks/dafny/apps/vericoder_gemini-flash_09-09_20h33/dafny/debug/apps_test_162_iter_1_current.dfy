predicate ValidInput(n: int, k: int, a: seq<int>)
{
    n >= 1 && k >= 1 && |a| == n &&
    (forall i :: 0 <= i < |a| ==> a[i] >= 1) &&
    (exists i :: 0 <= i < |a| && k % a[i] == 0)
}

predicate ValidBucket(k: int, bucketSize: int)
{
    bucketSize >= 1 && k % bucketSize == 0
}

function HoursNeeded(k: int, bucketSize: int): int
    requires ValidBucket(k, bucketSize)
{
    k / bucketSize
}

predicate IsOptimalChoice(k: int, a: seq<int>, chosenBucket: int)
{
    0 <= chosenBucket < |a| &&
    ValidBucket(k, a[chosenBucket]) &&
    (forall i :: 0 <= i < |a| && ValidBucket(k, a[i]) ==> a[i] <= a[chosenBucket])
}

// <vc-helpers>
lemma MaxBucketSizeIsOptimal(k: int, a: seq<int>, max_index: int)
  requires 0 <= max_index < |a|
  requires ValidBucket(k, a[max_index])
  requires forall i :: 0 <= i < |a| && ValidBucket(k, a[i]) ==> a[i] <= a[max_index]
  ensures IsOptimalChoice(k, a, max_index)
{
  // This lemma directly follows from the definition of IsOptimalChoice
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, k, a)
    ensures result >= 1
    ensures exists i :: IsOptimalChoice(k, a, i) && result == HoursNeeded(k, a[i])
// </vc-spec>
// <vc-code>
{
  var max_bucket_size := 0;
  var max_bucket_size_index := -1;

  // Since ValidInput ensures exists i :: 0 <= i < |a| && k % a[i] == 0
  // we are guaranteed to find at least one valid bucket.
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant -1 <= max_bucket_size_index < n
    invariant (max_bucket_size == 0 && max_bucket_size_index == -1) ||
              (max_bucket_size > 0 && max_bucket_size == a[max_bucket_size_index] && k % a[max_bucket_size_index] == 0)
    invariant (max_bucket_size_index >= 0) ==> (forall j :: 0 <= j < i && k % a[j] == 0 ==> a[j] <= max_bucket_size)
  {
    if k % a[i] == 0 { // Check if a[i] is a valid bucket size
      if a[i] > max_bucket_size {
        max_bucket_size := a[i];
        max_bucket_size_index := i;
      }
    }
    i := i + 1;
  }

  // After the loop, max_bucket_size_index must be a valid index
  // because ValidInput guarantees at least one `a[i]` divides `k`.
  assert max_bucket_size_index != -1;
  assert max_bucket_size == a[max_bucket_size_index];
  assert k % a[max_bucket_size_index] == 0;
  assert ValidBucket(k, a[max_bucket_size_index]);

  // Prove that a[max_bucket_size_index] is indeed the optimal choice
  // by showing it's the maximum among all valid bucket sizes.
  calc {
    true;
    forall j :: 0 <= j < |a| && ValidBucket(k, a[j]) ==> a[j] <= max_bucket_size;
      {
        var j := 0;
        while j < |a|
          invariant 0 <= j <= |a|
          invariant forall x :: 0 <= x < j && ValidBucket(k, a[x]) ==> a[x] <= max_bucket_size;
        {
          if ValidBucket(k, a[j]) {
            assert k % a[j] == 0;
            // The loop's invariant on `max_bucket_size` implies that
            // for any `x` iterated so far (which includes `j` if `j < i_final`),
            // if `a[x]` is a valid bucket, then `a[x] <= max_bucket_size`.
            // When `j` reaches its final value `|a|`, `max_bucket_size`
            // holds the maximum value among all valid `a[i]`.
            assert a[j] <= max_bucket_size;
          }
          j := j + 1;
        }
      }
  }

  // Use the helper lemma to confirm optimality
  MaxBucketSizeIsOptimal(k, a, max_bucket_size_index);
  assert IsOptimalChoice(k, a, max_bucket_size_index);

  result := HoursNeeded(k, a[max_bucket_size_index]);
}
// </vc-code>

