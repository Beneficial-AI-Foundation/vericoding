//ATOM


method InsertionSort (a:array<int>)
requires a!=null && a.Length>1 
ensures sorted(a, 0, a.Length) 
modifies a
{
  assume sorted(a, 0, a.Length);
}


//ATOM
 predicate sorted (a:array<int>, start:int, end:int) // all "before" end are sorted   
 requires a!=null    
 requires 0<=start<=end<=a.Length    
 reads a    
 {      
  forall j,k:: start<=j<k<end ==> a[j]<=a[k]
 }


//IMPL
method Main(){
 var a := new int[5];
 a[0],a[1],a[2],a[3],a[4] := 3,2,5,1,8;
 InsertionSort(a);
 print a[..];
}