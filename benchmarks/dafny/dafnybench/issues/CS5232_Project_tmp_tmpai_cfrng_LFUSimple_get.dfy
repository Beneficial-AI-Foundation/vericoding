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
method get(key: int) returns (value: int)
      requires Valid();
      modifies this;
      ensures Valid();
      ensures key !in cacheMap ==> value == -1;
      ensures forall e :: e in old(cacheMap) <==> e in cacheMap;
      ensures forall e :: e in old(cacheMap) ==> (old(cacheMap[e].0) == cacheMap[e].0);
      ensures key in cacheMap ==> value == cacheMap[key].0 && old(cacheMap[key].1) == cacheMap[key].1-1;
// </vc-spec>
// <vc-code>
{
      assert key in cacheMap ==> cacheMap[key].0 >= 0;
      if(key !in cacheMap) {
        value := -1;
      }
      else{
        assert key in cacheMap;
        assert cacheMap[key].0 >= 0;
        value := cacheMap[key].0;
        var oldFreq := cacheMap[key].1;
        var newV := (value, oldFreq + 1);
        cacheMap := cacheMap[key := newV];
      }
      print "after get: ";
      print cacheMap;
      print "\n";
      return value;
}
// </vc-code>

}