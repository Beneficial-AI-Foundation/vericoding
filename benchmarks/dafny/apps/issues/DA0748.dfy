// <vc-preamble>
predicate ValidInput(n: int, a: seq<int>, b: string)
{
  n >= 5 && |a| == n && |b| == n && 
  forall k :: 0 <= k < |b| ==> (b[k] == '0' || b[k] == '1')
}

predicate ValidOutput(result: (int, int))
{
  result.0 >= -1000000000 && result.1 <= 1000000000 && result.0 <= result.1
}

function MaxInRange(a: seq<int>, start: int, end: int): int
  requires 0 <= start < end <= |a|
  decreases end - start
{
  if start + 1 == end then a[start]
  else if a[start] > MaxInRange(a, start + 1, end) then a[start]
  else MaxInRange(a, start + 1, end)
}

function MinInRange(a: seq<int>, start: int, end: int): int
  requires 0 <= start < end <= |a|
  decreases end - start
{
  if start + 1 == end then a[start]
  else if a[start] < MinInRange(a, start + 1, end) then a[start]
  else MinInRange(a, start + 1, end)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>, b: string) returns (result: (int, int))
  requires ValidInput(n, a, b)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
    var r := 1000000000;
    var l := -1000000000;

    var i := 4;
    while i < n
        invariant 4 <= i <= n
        invariant l >= -1000000000
        invariant r <= 1000000000
    {
        if i > 0 && b[i-1] != b[i] {
            if b[i] == '0' {
                // Find min of a[i-4], a[i-3], a[i-2], a[i-1], a[i]
                var minVal := a[i-4];
                var j := i-3;
                while j <= i
                    invariant i-3 <= j <= i+1
                    invariant minVal <= a[i-4]
                    invariant forall k :: i-4 <= k < j ==> minVal <= a[k]
                {
                    if a[j] < minVal {
                        minVal := a[j];
                    }
                    j := j + 1;
                }
                if minVal - 1 < r {
                    r := minVal - 1;
                }
            } else {
                // Find max of a[i-4], a[i-3], a[i-2], a[i-1], a[i]
                var maxVal := a[i-4];
                var j := i-3;
                while j <= i
                    invariant i-3 <= j <= i+1
                    invariant maxVal >= a[i-4]
                    invariant forall k :: i-4 <= k < j ==> maxVal >= a[k]
                {
                    if a[j] > maxVal {
                        maxVal := a[j];
                    }
                    j := j + 1;
                }
                if maxVal + 1 > l {
                    l := maxVal + 1;
                }
            }
        }
        i := i + 1;
    }

    // Ensure l <= r for valid output
    if l > r {
        l := -1000000000;
        r := 1000000000;
    }

    result := (l, r);
}
// </vc-code>
