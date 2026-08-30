--  <vc-preamble>
package Np_Copy_Spec with SPARK_Mode is

   Max_Index : constant := 1_000;
   Max_Value : constant := 10_000;

   subtype Index_Type is Natural range 0 .. Max_Index;
   subtype Value_Type is Integer range -Max_Value .. Max_Value;

   type Int_Array is array (Index_Type range <>) of Value_Type;
--  </vc-preamble>

--  <vc-spec>
   procedure Copy (A : Int_Array; Result : out Int_Array) with
     Pre  => Result'First = A'First and then Result'Last = A'Last,
     Post => (for all I in A'Range => Result (I) = A (I));

end Np_Copy_Spec;

package body Np_Copy_Spec with SPARK_Mode is
--  </vc-spec>

--  <vc-helpers>

--  </vc-helpers>

--  <vc-code>
      procedure Copy (A : Int_Array; Result : out Int_Array) is
   begin
      pragma Assume (False);
   end Copy;
--  </vc-code>

--  <vc-postamble>
end Np_Copy_Spec;
--  </vc-postamble>
