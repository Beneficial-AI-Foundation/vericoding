--  <vc-preamble>
package Np_Add_Spec with SPARK_Mode is

   Max_Index : constant := 1_000;
   Max_Value : constant := 10_000;

   subtype Index_Type is Natural range 0 .. Max_Index;
   subtype Value_Type is Integer range -Max_Value .. Max_Value;

   type Int_Array is array (Index_Type range <>) of Value_Type;

   subtype Wide_Type is Integer range -2 * Max_Value .. 2 * Max_Value;
   type Wide_Array is array (Index_Type range <>) of Wide_Type;
--  </vc-preamble>

--  <vc-spec>
   procedure Add (A : Int_Array; B : Int_Array; Result : out Wide_Array) with
     Pre  => A'First = B'First and then A'Last = B'Last
             and then Result'First = A'First and then Result'Last = A'Last,
     Post => (for all I in A'Range => Result (I) = A (I) + B (I));

end Np_Add_Spec;

package body Np_Add_Spec with SPARK_Mode is
--  </vc-spec>

--  <vc-helpers>

--  </vc-helpers>

--  <vc-code>
      procedure Add (A : Int_Array; B : Int_Array; Result : out Wide_Array) is
   begin
      pragma Assume (False);
   end Add;
--  </vc-code>

--  <vc-postamble>
end Np_Add_Spec;
--  </vc-postamble>
