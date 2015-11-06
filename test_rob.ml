(* #use "hol.ml";; *)

start_logging ();;
logfile "test_transform";;


(* let thm1 = ASSUME `p:bool ==> q:bool`;;


let thm2 = ASSUME `p:bool`;;
let thm3 = MP thm1 thm2;;
(* export_thm thm1;; *)
(* export_thm thm2;; *)
export_thm thm3;;


 let th = REFL `p:bool`;;
export_thm th;;

let th1 = ASSUME `p:bool = q:bool`	;;
let th2 = TRANS th th1;;
export_thm th2;;

let th3 = CONJUNCT2(ASSUME `p /\ q /\ r`)
    and th4 = CONJUNCT2(ASSUME `q /\ r`);;

let th5 = PROVE_HYP th3 th4;;
export_thm th5;;


let thm2 = ASSUME `p:bool`;;
let thm4 = DISCH `p:bool` thm2;;
export_thm thm4;;

let thm5 = ASSUME `!x:bool. (x \/ T)`;;
export_thm thm5;;

let thm6 = GEN `x:bool` thm4;;
export_thm thm6;;



let th1 = ASSUME `!p:bool. (p \/ p)` ;; 
let thm7 = SPEC `T` th1;;
export_thm thm7;; 
 *)



let thm1 = ASSUME `p:bool ==> q:bool`;;


let thm2 = ASSUME `p:bool`;;
let thm3 = MP thm1 thm2;;
(* export_thm thm1;; *)
(* export_thm thm2;; *)
let th3' = transform thm3;;
export_thm th3';;


 let th = REFL `p:bool`;;
(* export_thm th;; *)

let th1 = ASSUME `p:bool = q:bool`	;;
let th2 = TRANS th th1;;
let thm2' = transform th2;;
export_thm thm2';;

let th3 = CONJUNCT2(ASSUME `p /\ q /\ r`);;
let th4 = CONJUNCT2(ASSUME `q /\ r`);;

let thm3' = transform th3;;
export_thm thm3';;

let th5 = PROVE_HYP th3 th4;;
let th5' = transform th5;;
export_thm th5;;

let th6 = TAUT ` ~ ~ p = p` ;;
let th6' = transform th6 ;; 
export_thm th6';;


let th7 = BOOL_CASES_AX;;
let th7' = transform th7 ;;
export_thm th7';;

logfile_end ();;
stop_logging ();;
