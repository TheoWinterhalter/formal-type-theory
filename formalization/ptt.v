Require Import tt.

Module Make (ConfigReflection : CONFIG_REFLECTION) :=
  MakeParanoid(ConfigReflection).