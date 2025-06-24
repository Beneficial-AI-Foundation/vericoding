// ATOM 
function SumR(s:seq<int>):int
{
    if (s==[]) then 0
    else SumR(s[..|s|-1])+s[|s|-1]
}


// ATOM 

function SumL(s:seq<int>):int
{
    if (s==[]) then 0
    else s[0]+SumL(s[1..])
}



//ATOM_PLACEHOLDER_concatLast
//ATOM_PLACEHOLDER_concatFirst

//ATOM_PLACEHOLDER_unknown_369 SumByPartsR(s:seq<int>,t:seq<int>)
ensures SumR(s+t) == SumR(s)+SumR(t)
{ if (t==[])
     {assert s+t == s;}
  else if (s==[])
     {assert s+t==t;}   
   else
     { 
       calc =={
        SumR(s+t);
        SumR((s+t)[..|s+t|-1])+(s+t)[|s+t|-1];
        SumR((s+t)[..|s+t|-1])+t[|t|-1];
        {concatLast(s,t);}
        SumR(s+t[..|t|-1])+t[|t|-1];
        {SumByPartsR(s,t[..|t|-1]);}
        SumR(s)+SumR(t[..|t|-1])+t[|t|-1];
        SumR(s)+SumR(t);

       }
     }


}


//ATOM_PLACEHOLDER_unknown_875 SumByPartsL(s:seq<int>,t:seq<int>)
ensures SumL(s+t) == SumL(s)+SumL(t)
//Prove this
{
  if(t==[]){
  }
  else if(s==[]){
  }
  else{
      calc == {
        SumL(s+t);
        (s+t)[0] + SumL((s+t)[1..]);
        s[0] + SumL((s+t)[1..]);
        {concatFirst(s,t);}
        s[0] + SumL(s[1..] + t);
        {SumByPartsL(s[1..], t);}
        s[0] + SumL(s[1..]) + SumL(t);
      }
  }
}




//ATOM_PLACEHOLDER_unknown_1289 equalSumR(s:seq<int>,i:int,j:int)
requires 0<=i<=j<=|s|
ensures  SumR(s[i..j])==SumL(s[i..j])
//Prove this
{
  if(s==[]){
  }else{
    if(i==j){
    }
    else{
      calc == {
        SumR(s[i..j]);
        {
        }
        SumR(s[i..j-1]) + s[j-1];
        {equalSumR(s, i, j-1);}
        SumL(s[i..j-1]) + s[j-1];
        {assert s[j-1] == SumL([s[j-1]]);}
        SumL(s[i..j-1]) + SumL([s[j-1]]);
        {SumByPartsL(s[i..j-1], [s[j-1]]);}
        SumL(s[i..j-1] + [s[j-1]]);
        {
        }
        SumL(s[i..j]);
        /*SumR(s[i..j-1])+SumR(s[j..j]);
        SumR(s[i..j-1]) + s[j..j];
        SumL(s);*/
      }
    }
  }
}


// ATOM 


lemma equalSumsV() 
ensures forall v:array<int>,i,j | 0<=i<=j<=v.Length :: SumR(v[i..j])==SumL(v[i..j])
 //proving the forall
  { forall v:array<int>,i,j | 0<=i<=j<=v.Length
    ensures SumR(v[i..j])==SumL(v[i..j])
    {equalSumR(v[..],i,j);}
  }



//ATOM_PLACEHOLDER_SumV


//ATOM_PLACEHOLDER_ArrayFacts
  

//ATOM_PLACEHOLDER_sumElems

// SPEC 

method sumElemsB(v:array<int>) returns (sum:int)
//ensures sum==SumL(v[0..v.Length])
ensures sum==SumR(v[0..v.Length])
{
}
















