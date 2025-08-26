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

// <vc-helpers>
// </vc-helpers>

method getLFUKey() returns (lfuKey : int) 
      requires Valid();
      requires |cacheMap| > 0;
      ensures Valid();
      ensures lfuKey in cacheMap;
      ensures forall k :: k in cacheMap.Items ==> cacheMap[lfuKey].1 <= cacheMap[k.0].1;
// <vc-code>
{
  assume false;
}
// </vc-code>

}