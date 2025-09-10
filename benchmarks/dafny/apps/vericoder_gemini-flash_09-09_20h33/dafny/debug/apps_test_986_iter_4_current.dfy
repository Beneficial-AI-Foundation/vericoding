predicate ValidInput(n: int, k: int, requests: seq<int>)
{
    n >= 1 && k >= 1 && |requests| == n &&
    forall i :: 0 <= i < |requests| ==> 1 <= requests[i] <= n
}

predicate ValidSolution(n: int, k: int, requests: seq<int>, cost: int)
{
    ValidInput(n, k, requests) && cost >= 0 && cost <= n
}

// <vc-helpers>
predicate {:opaque} IsPresent(s: seq<int>, x: int) {
    exists i :: 0 <= i < |s| && s[i] == x
}

function {:opaque} CountDistinct(s: seq<int>): int {
    var distinct_count := 0;
    var seen: set<int> := {};
    for x in s {
        if x !in seen {
            distinct_count := distinct_count + 1;
            seen := seen + {x};
        }
    }
    return distinct_count;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, requests: seq<int>) returns (cost: int)
    requires ValidInput(n, k, requests)
    ensures ValidSolution(n, k, requests, cost)
// </vc-spec>
// <vc-code>
{
    var cache: seq<int> := [];
    var currentCost: int := 0;

    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant 0 <= currentCost <= i
        invariant forall x :: IsPresent(cache, x) ==> (exists j :: 0 <= j < i && requests[j] == x) // items in cache must be from processed requests
        invariant forall x :: IsPresent(cache, x) ==> 1 <= x <= n // items in cache are valid
        invariant |cache| <= k // cache size constraint
        invariant CountDistinct(cache) == |cache| // cache contains distinct elements
    {
        var request_page := requests[i];

        if !IsPresent(cache, request_page) {
            // Page fault occurs
            currentCost := currentCost + 1;

            if |cache| == k {
                // Cache is full, evict the least recently used page
                cache := cache[1..|cache|] + [request_page];
            } else {
                // Cache is not full, just add the new page
                cache := cache + [request_page];
            }
        } else {
            // Page hit, move the page to the end (most recently used)
            var idx := 0;
            while idx < |cache| && cache[idx] != request_page
                invariant 0 <= idx <= |cache|
                invariant forall j :: 0 <= j < idx ==> cache[j] != request_page
            {
                idx := idx + 1;
            }
            // `idx` is guaranteed to be found because `IsPresent` is true
            // Remove from current position and append to end
            cache := cache[0..idx] + cache[idx+1..|cache|] + [request_page];
        }
        i := i + 1;
    }
    cost := currentCost;
}
// </vc-code>

