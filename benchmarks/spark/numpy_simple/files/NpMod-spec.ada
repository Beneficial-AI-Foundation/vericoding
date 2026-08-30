--  <vc-preamble>
package Np_Mod_Spec with SPARK_Mode is

   Max_Index : constant := 1_000;
   Max_Value : constant := 10_000;

   subtype Index_Type is Natural range 0 .. Max_Index;
   subtype Value_Type is Integer range -Max_Value .. Max_Value;

   type Int_Array is array (Index_Type range <>) of Value_Type;

   --  Dafny's "%" on int is Euclidean remainder (always non-negative), which
   --  coincides with Ada's "mod" for a positive divisor.
--  </vc-preamble>

--  <vc-spec>
   procedure Mod_Vec (A : Int_Array; B : Int_Array; Result : out Int_Array) with
     Pre  => A'First = B'First and then A'Last = B'Last
             and then Result'First = A'First and then Result'Last = A'Last
             and then (for all I in B'Range => B (I) > 0),
     Post => (for all I in A'Range => Result (I) = A (I) mod B (I));

end Np_Mod_Spec;

package body Np_Mod_Spec with SPARK_Mode is
--  </vc-spec>

--  <vc-helpers>

--  </vc-helpers>

--  <vc-code>
      procedure Mod_Vec (A : Int_Array; B : Int_Array; Result : out Int_Array) is
   begin
      pragma Assume (False);
   end Mod_Vec;
--  </vc-code>

--  <vc-postamble>
end Np_Mod_Spec;
--  </vc-postamble>
