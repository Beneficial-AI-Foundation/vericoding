// <vc-preamble>
class LFUCache {

    var capacity : int;
    var cacheMap : map<int, (int, int)>; //key -> {value, freq}

    constructor(capacity: int)
      requires capacity > 0;
      ensures Valid();
    {
      this.capacity := capacity;
      this.cacheMap := map[];
    }

    predicate Valid()
      reads this;
      // reads this.freqMap.Values;
    {
      // general value check
      this.capacity > 0 &&
      0 <= |cacheMap| <= capacity &&
      (|cacheMap| > 0 ==> (forall e :: e in cacheMap ==> cacheMap[e].1 >= 1)) && // frequency should always larger than 0
      (|cacheMap| > 0 ==> (forall e :: e in cacheMap ==> cacheMap[e].0 >= 0)) // only allow positive values
    }
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method getLFUKey() returns (lfuKey : int) 
      requires Valid();
      requires |cacheMap| > 0;
      ensures Valid();
      ensures lfuKey in cacheMap;
      ensures forall k :: k in cacheMap.Items ==> cacheMap[lfuKey].1 <= cacheMap[k.0].1;
// </vc-spec>
// <vc-code>
{
      var items := cacheMap.Items;
      var seenItems := {};

      var anyItem :| anyItem in items;
      var minFreq := anyItem.1.1;
      lfuKey := anyItem.0;

      while items != {}
        decreases |items|;
        invariant cacheMap.Items >= items;
        invariant cacheMap.Items >= seenItems;
        invariant cacheMap.Items == seenItems + items;
        invariant lfuKey in cacheMap;
        invariant cacheMap[lfuKey].1 == minFreq;
        invariant forall e :: e in seenItems ==> minFreq <= e.1.1;
        invariant forall e :: e in seenItems ==> minFreq <= cacheMap[e.0].1;
        invariant forall e :: e in seenItems ==> cacheMap[lfuKey].1 <= cacheMap[e.0].1;
        invariant exists e :: e in seenItems + items ==> minFreq == e.1.1;
      {
        var item :| item in items;

        if (item.1.1 < minFreq) {
          lfuKey := item.0;
          minFreq := item.1.1;
        }
        items := items - { item };
        seenItems := seenItems + { item };
      }
      assert seenItems == cacheMap.Items;
      assert cacheMap[lfuKey].1 == minFreq;
      assert forall e :: e in seenItems ==> minFreq <= e.1.1;
      assert forall e :: e in cacheMap.Items ==> minFreq <= e.1.1;
      assert forall k :: k in seenItems ==> cacheMap[lfuKey].1 <= cacheMap[k.0].1;
      assert forall k :: k in cacheMap.Items ==> cacheMap[lfuKey].1 <= cacheMap[k.0].1;
      // assert forall k :: k in cacheMap ==> cacheMap[lfuKey].1 <= cacheMap[k].1; // ????
      return lfuKey;
}
// </vc-code>

}