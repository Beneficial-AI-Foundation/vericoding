/-
  Port of vericoding_dafnybench_0392_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Max (i1 : Int) (i2 : Int) : Int :=
  sorry  -- TODO: implement function body

def Min (i1 : Int) (i2 : Int) : Int :=
  sorry  -- TODO: implement function body

def RoundUp (i : Int) (r : Nat) : Int :=
  sorry  -- TODO: implement function body

function MaxUnsignedN(n:nat) : (r:nat)
  sorry  -- TODO: implement function body

function Pow(n:nat, k:nat) : (r:nat)
  sorry  -- TODO: implement function body

def Div (lhs : Int) (rhs : Int) : Int :=
  sorry  -- TODO: implement function body

def Rem (lhs : Int) (rhs : Int) : Int :=
  sorry  -- TODO: implement function body

function Log2(v:u8) : (r:nat)
  sorry  -- TODO: implement function body

def NthUint8 (v : u16) (k : Nat) : u8 :=
  sorry  -- TODO: implement function body

function Log2(v:u16) : (r:nat)
  sorry  -- TODO: implement function body

function Log256(v:u16) : (r:nat)
  sorry  -- TODO: implement function body

function ToBytes(v:u16) : (r:seq<u8>)
  sorry  -- TODO: implement function body

def Read (bytes : seq<u8>) (address : Nat) : u16 :=
  sorry  -- TODO: implement function body

def NthUint16 (v : u32) (k : Nat) : u16 :=
  sorry  -- TODO: implement function body

function Log2(v:u32) : (r:nat)
  sorry  -- TODO: implement function body

function Log256(v:u32) : (r:nat)
  sorry  -- TODO: implement function body

function ToBytes(v:u32) : (r:seq<u8>)
  sorry  -- TODO: implement function body

def Read (bytes : seq<u8>) (address : Nat) : u32 :=
  sorry  -- TODO: implement function body

def NthUint32 (v : u64) (k : Nat) : u32 :=
  sorry  -- TODO: implement function body

function Log2(v:u64) : (r:nat)
  sorry  -- TODO: implement function body

function Log256(v:u64) : (r:nat)
  sorry  -- TODO: implement function body

function ToBytes(v:u64) : (r:seq<u8>)
  sorry  -- TODO: implement function body

def Read (bytes : seq<u8>) (address : Nat) : u64 :=
  sorry  -- TODO: implement function body

def NthUint64 (v : u128) (k : Nat) : u64 :=
  sorry  -- TODO: implement function body

function Log2(v:u128) : (r:nat)
  sorry  -- TODO: implement function body

function Log256(v:u128) : (r:nat)
  sorry  -- TODO: implement function body

function ToBytes(v:u128) : (r:seq<u8>)
  sorry  -- TODO: implement function body

def Read (bytes : seq<u8>) (address : Nat) : u128 :=
  sorry  -- TODO: implement function body

def Shl (lhs : u256) (rhs : u256) : u256 :=
  var lbv := lhs as bv256; // NOTE: unclear whether shifting is optimal choice here. var res := if rhs < 256 then (lbv << rhs) else 0; // res as u256

def Shr (lhs : u256) (rhs : u256) : u256 :=
  sorry  -- TODO: implement function body

function Log2(v:u256) : (r:nat)
  sorry  -- TODO: implement function body

function Log256(v:u256) : (r:nat)
  sorry  -- TODO: implement function body

def NthUint128 (v : u256) (k : Nat) : u128 :=
  sorry  -- TODO: implement function body

def NthUint8 (v : u256) (k : Nat) : u8 :=
  sorry  -- TODO: implement function body

def Read (bytes : seq<u8>) (address : Nat) : u256 :=
  sorry  -- TODO: implement function body

function ToBytes(v:u256) : (r:seq<u8>)
  sorry  -- TODO: implement function body

def SignExtend (v : u256) (k : Nat) : u256 :=
  sorry  -- TODO: implement function body

def Div (lhs : i256) (rhs : i256) : i256 :=
  sorry  -- TODO: implement function body

def Rem (lhs : i256) (rhs : i256) : i256 :=
  sorry  -- TODO: implement function body

def Sar (lhs : i256) (rhs : u256) : i256 :=
  sorry  -- TODO: implement function body

def asI256 (w : u256) : i256 :=
  sorry  -- TODO: implement function body

def fromI256 (w : Int.i256) : u256 :=
  sorry  -- TODO: implement function body

end DafnyBenchmarks