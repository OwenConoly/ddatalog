From Stdlib Require Import List ZArith Lia String.
From DatalogRocq Require Import Examples.SouffleGeneratedRocq.Unitprop1 DistributedDatalogToHardwareCompiler StringDatalogParams StringGridCompiler.
Import ListNotations.

(* Compilation *)

Definition program_to_compile : list rule := computed_program.

(* For purposes of benchmarking this is so we can also compile to a single node *)
Definition one_node_layout : list (node_id * list nat) := [ ([0;0], [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42; 43; 44; 45; 46; 47; 48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 58; 59; 60; 61; 62; 63; 64; 65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76; 77; 78; 79; 80; 81; 82; 83; 84; 85; 86; 87; 88; 89; 90; 91; 92; 93; 94; 95; 96; 97; 98; 99; 100; 101; 102; 103; 104; 105; 106; 107; 108; 109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 120; 121; 122; 123; 124; 125; 126; 127; 128; 129; 130; 131; 132; 133; 134; 135; 136; 137; 138; 139; 140; 141; 142; 143; 144; 145; 146; 147; 148; 149; 150; 151; 152; 153; 154; 155; 156; 157; 158; 159; 160; 161; 162; 163; 164; 165; 166; 167; 168; 169; 170; 171; 172; 173; 174; 175; 176; 177; 178; 179; 180; 181; 182; 183; 184; 185; 186; 187; 188; 189; 190; 191; 192; 193; 194; 195; 196; 197; 198; 199; 200; 201; 202; 203; 204; 205; 206; 207; 208; 209; 210; 211; 212; 213; 214; 215; 216; 217; 218; 219; 220; 221; 222; 223; 224; 225; 226; 227; 228; 229; 230; 231; 232; 233; 234; 235; 236; 237; 238; 239; 240; 241; 242; 243; 244; 245]) ].

(* Actual compiler assigned layout *)
Definition layout : list (node_id * list nat) := 
  [ ([0;0], [71;72;73;74;75;76;77;78;79;80;81;82;84;85;86;87;88;89;90;91;102;103;104;105;106;107;108;109;110]); ([0;1], [23;24;25;26;27;28;29;30;31;32;33;35;83;92;206;207;208;209;210;211;212;213;214;215;216;217;218;219;220;221;222]); ([0;2], [14;15;16;17;18;19;20;21;45;46;47;48;49;50;51;52;53;54;55;56;57]); ([1;0], [146;147;148;149;150;151;152;153;154;155;156;157;158;189;190;191;192;193;194;195;196;197;198;199;200;201;202;204;205]); ([1;1], [2;3;12;13;22;34;36;37;38;39;40;41;42;43;44;58;59;60;61;62;63;64;65;66;67;68;69;70;101;203;244]); ([1;2], [131;223;224;225;226;227;228;229;230;231;232;233;234;235;236;237;238;239;240;241;242;243]); ([2;0], [1;4;159;160;161;162;163;164;165;166;167;168;169;171;172;173;174;175;176;177;178;179;180;181;182;183;184;185;186;187;188]); ([2;1], [0;5;6;7;8;9;10;11;93;94;95;96;97;98;99;100;133;134;135;136;137;138;139;140;141;142;143;144;145;170]); ([2;2], [111;112;113;114;115;116;117;118;119;120;121;122;123;124;125;126;127;128;129;130;132;245]) ].

Definition topo_dims : GridGraph.Dimensions := [3; 3].

(* TODO: no designated input/output nodes (the declared fact_producers/fact_consumers, if any,
   don't cover every produced relation under the output-sink gate), so this uses
   [all_io_locations] -- every grid node is an input AND output for every relation.
   Replace with the real input/output nodes. *)
Definition compiled_unitprop1 := compile_program program_to_compile layout (all_io_locations program_to_compile layout topo_dims) (all_io_locations program_to_compile layout topo_dims) topo_dims 100.

Eval vm_compute in compiled_unitprop1.