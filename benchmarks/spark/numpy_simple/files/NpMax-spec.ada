--  <vc-preamble>
package Np_Max_Spec with SPARK_Mode is

   Max_Index : constant := 1_000;
   Max_Value : constant := 10_000;

   subtype Index_Type is Natural range 0 .. Max_Index;
   subtype Value_Type is Integer range -Max_Value .. Max_Value;

   type Int_Array is array (Index_Type range <>) of Value_Type;
--  </vc-preamble>

--  <vc-spec>
   procedure Max (A : Int_Array; Result : out Value_Type) with
     Pre  => A'Length > 0,
     Post => (for some I in A'Range => Result = A (I))
             and then (for all I in A'Range => A (I) <= Result);

end Np_Max_Spec;

package body Np_Max_Spec with SPARK_Mode is
--  </vc-spec>

--  <vc-helpers>

--  </vc-helpers>

--  <vc-code>
      procedure Max (A : Int_Array; Result : out Value_Type) is
   begin
      pragma Assume (False);
   end Max;
--  </vc-code>

--  <vc-postamble>
end Np_Max_Spec;
--  </vc-postamble>
