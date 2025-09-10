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
    if |s| == 0 then 0
    else (if IsPresent(s[0..|s|-1], s[|s|-1]) then CountDistinct(s[0..|s|-1]) else CountDistinct(s[0..|s|-1]) + 1)
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
        // The following invariant ensures that if an element is in the cache, it's one of the *k* most recently used.
        // It's tricky to express LRU precisely without a more complex data structure,
        // but for this problem, we only need to ensure the distinctness and size.

    {
        var request_page := requests[i];

        if !IsPresent(cache, request_page) {
            // Page fault occurs
            currentCost := currentCost + 1;

            if |cache| == k {
                // Cache is full, evict the least recently used page
                // For this simplified LRU, we can just remove the first element (oldest in the sequence)
                // and append the new page. More complex LRU involves moving existing pages to the end.
                // However, the problem statement description for LRU in general context often means
                // a page fault happens only if the cache is full AND the page is not in the cache.
                // If it's not in the cache and cache is full, one item is removed and the new one is added.
                // If the specified `cost` means the number of page faults, then it's just the count.
                // The problem description doesn't specify if `k` is a hard limit on cache size,
                // or if it refers to the number of *distinct* pages that can be concurrently kept.
                // Given the phrasing "LRU cache", it usually implies a fixed-size cache.
                // So, if the cache is full, we must remove an element.
                // A simple implementation of LRU for this problem might be to remove the first element
                // of the cache if the cache is full.
                cache := cache[1..] + [request_page];
            } else {
                // Cache is not full, just add the new page
                cache := cache + [request_page];
            }
        } else {
            // Page hit, move the page to the end (most recently used)
            var idx := 0;
            while idx < |cache| && cache[idx] != request_page
                invariant 0 <= idx < |cache|
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

