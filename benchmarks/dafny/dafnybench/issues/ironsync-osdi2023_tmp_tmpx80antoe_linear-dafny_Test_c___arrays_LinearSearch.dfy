// <vc-preamble>
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cpp "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint32 = i:int | 0 <= i < 0x100000000
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method LinearSearch(a: array<uint32>, len:uint32, key: uint32) returns (n: uint32)
  requires a.Length == len as int
  ensures 0 <= n <= len
  ensures n == len || a[n] == key
// </vc-spec>
// <vc-code>
{
  n := 0;
  while n < len
    invariant n <= len
  {
    if a[n] == key {
      return;
    }
    n := n + 1;
  }
}
// </vc-code>

method PrintArray<A>(a:array?<A>, len:uint32)
  requires a != null ==> len as int == a.Length
{
  if (a == null) {
    print "It's null\n";
  } else {
    var i:uint32 := 0;
    while i < len {
      print a[i], " ";
      i := i + 1;
    }
    print "\n";
  }
}

datatype ArrayDatatype = AD(ar: array<uint32>)