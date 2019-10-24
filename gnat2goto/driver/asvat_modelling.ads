with Types;                   use Types;
with Atree;                   use Atree;
with Sinfo;                   use Sinfo;
with Einfo;                   use Einfo;
with Sem_Util;                use Sem_Util;
with Snames;                  use Snames;
package ASVAT_Modelling is
   Non_Det         : constant String := "Non_Det";
   Non_Det_In_Type : constant String := "Non_Det_In_Type";
   From_Unit       : constant String := "From_Unit";

   Model_List : constant String :=
     (""
        & Non_Det          & '#'
        & Non_Det_In_Type  & '#'
        & From_Unit  & '#'
     );

   type Model_Index is range 0 .. Model_List'Length;

   function Find_Model (S : String) return Model_Index;

   function Get_Import_Convention (N : Node_Id) return String
   with Pre => Nkind (N) = N_Pragma and then
               Get_Pragma_Id (N) = Pragma_Import;

   function Get_Import_External_Name (N : Node_Id) return String
   with Pre => Nkind (N) = N_Pragma and then
               Get_Pragma_Id (N) = Pragma_Import;
   --  Returns null string if the External_Name parameter is not present.

   function Get_Import_Link_Name (N : Node_Id) return String
   with Pre => Nkind (N) = N_Pragma and then
               Get_Pragma_Id (N) = Pragma_Import;
   --  Returns null string if the Link_Name parameter is not present.

   function Is_Model (E : Entity_Id) return Boolean;

   function Is_Model_String (S : String) return Boolean;

   function Is_Model_Sort (E : Entity_Id; Model : String) return Boolean;

   procedure Make_Model (E : Entity_Id)
   with Pre => Is_Model (E);

   function Replace_Local_Object_With_Import
     (E : Entity_Id; Print_Message : Boolean) return String
     with Pre => Ekind (E) in E_Variable | E_Constant;

   function Replace_Local_Type_With_Import
     (E : Entity_Id; Print_Message : Boolean) return String
     with Pre => Ekind (E) in E_Variable | E_Constant;

end ASVAT_Modelling;
