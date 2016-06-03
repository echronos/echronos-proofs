(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory EChronos_arm_sched_prop_bare

imports
  EChronos_arm_sched_prop_state
  OG_Bare
begin

definition 
  control:: "routine \<Rightarrow> ('a state_ext) bare_com \<Rightarrow> ('a state_ext) bare_com" 
where
  "control r c \<equiv> await_paint \<lbrace>\<acute>AT = r\<rbrace> c"

definition
  can_interrupt :: "'a state_ext \<Rightarrow> routine \<Rightarrow> bool"
where
  "can_interrupt x i \<equiv>
    i \<in> EIT x - set (ATStack x) \<and> i \<in> interrupt_policy (AT x)"

definition
  can_interrupt' :: "'a state_ext \<Rightarrow> routine \<Rightarrow> bool"
where
  "can_interrupt' x i \<equiv>
    i \<in> EIT x - set (ATStack x) \<and> i \<in> interrupt_policy (hd (ATStack x))"

definition
  ITake ::" nat \<Rightarrow> ('a state_ext) bare_com"
where
  "ITake i \<equiv>
    AWAIT \<acute>can_interrupt i
    THEN
     \<acute>ATStack := \<acute>AT # \<acute>ATStack,, \<acute>AT := i
    END"
    
definition
  IRet :: "('a state_ext) bare_com"
where
  "IRet \<equiv>
    IF \<acute>svc\<^sub>aReq \<and> \<acute>can_interrupt' svc\<^sub>a
      THEN \<acute>AT := svc\<^sub>a,, \<acute>svc\<^sub>aReq := False
      ELSE \<acute>AT := hd \<acute>ATStack,, \<acute>ATStack := tl \<acute>ATStack
    FI"

definition
  svc\<^sub>aTake :: "('a state_ext) bare_com"
where
  "svc\<^sub>aTake \<equiv> 
    AWAIT \<acute>svc\<^sub>aReq \<and> \<acute>can_interrupt svc\<^sub>a
    THEN
      \<acute>ATStack := \<acute>AT # \<acute>ATStack,,
      \<acute>AT := svc\<^sub>a,, \<acute>svc\<^sub>aReq := False
    END"

definition
  hardware_init :: "('a state_ext) bare_com"
where
  "hardware_init \<equiv>
   \<acute>EIT := I';;
   \<acute>svc\<^sub>aReq := False;;
   \<acute>AT := user0;;
   \<acute>ATStack := []"

definition
  interleaving ::
    " ('a state_ext) bare_com \<Rightarrow> (nat \<Rightarrow> ('a state_ext) bare_com)
     \<Rightarrow> (nat \<Rightarrow> ('a state_ext) bare_com)
        \<Rightarrow> ('a state_ext) bare_com \<Rightarrow> ('a state_ext) bare_com
        \<Rightarrow> ('a state_ext) bare_com"
where
 "interleaving app_init app_code handler_code svc\<^sub>a_code svc\<^sub>s_code \<equiv>
   hardware_init;;
   app_init;;
  (COBEGIN
     WHILE True DO svc\<^sub>aTake OD
   \<parallel> WHILE True DO control svc\<^sub>a svc\<^sub>a_code OD
   \<parallel> WHILE True DO control svc\<^sub>s svc\<^sub>s_code OD
   \<parallel> SCHEME [user0 \<le> i < user0 + nbRoutines]
     IF i \<in> I THEN
       WHILE True DO ITake i;; control i (handler_code i) OD
     ELSE
       WHILE True DO control i (app_code i) OD
     FI
  COEND)"

definition "SVC_now     \<equiv> \<acute>ATStack := \<acute>AT # \<acute>ATStack,, \<acute>AT := svc\<^sub>s"
definition "svc\<^sub>aEnable  \<equiv> \<acute>EIT := \<acute>EIT \<union> {svc\<^sub>a}"
definition "svc\<^sub>aDisable \<equiv> \<acute>EIT := \<acute>EIT - {svc\<^sub>a}"
definition "svc\<^sub>aRequest \<equiv> \<acute>svc\<^sub>aReq := True"

definition
  context_switch:: "bool \<Rightarrow> eChronos_state bare_com"
where
  "context_switch preempt_enabled \<equiv>
    \<acute>contexts := \<acute>contexts (\<acute>curUser \<mapsto> (preempt_enabled, \<acute>ATStack));;
    \<acute>curUser := the \<acute>nextT;;
    \<acute>ATStack := snd (the (\<acute>contexts (\<acute>curUser)));;
    IF fst (the (\<acute>contexts (\<acute>curUser)))
      THEN svc\<^sub>aEnable
      ELSE svc\<^sub>aDisable FI"
      
definition
  schedule
where
  "schedule \<equiv>
    \<acute>nextT := None;;
    WHILE \<acute>nextT = None
    DO
      \<acute>E_tmp := \<acute>E;;
      \<acute>R := handle_events \<acute>E_tmp \<acute>R;;
      \<acute>E := \<acute>E - \<acute>E_tmp;;
      \<acute>nextT := sched_policy(\<acute>R)
    OD"
    
definition 
  eChronos_init ::"eChronos_state bare_com"
where
  "eChronos_init \<equiv>
   \<acute>curUser := user0;;
   \<acute>contexts := (\<lambda>n. if n\<in>U then Some (True, [n]) else None);;
   \<acute>R := (\<lambda>n. if n\<in>U then Some True else None);;
   \<acute>E := {};;
   \<acute>E_tmp := {};;
   \<acute>nextT := None;;
   \<acute>ghostP := False;;
   \<acute>ghostS := False;;
   \<acute>ghostU := (\<lambda>_. User)"
    
definition 
  eChronos_app_code
where
  "eChronos_app_code i \<equiv>
      \<acute>userSyscall :\<in> {SignalSend, Block};;
      IF \<acute>userSyscall = SignalSend
      THEN
        \<langle>\<acute>ghostU := \<acute>ghostU (i := Syscall),, svc\<^sub>aDisable\<rangle>;;
        (\<acute>R :\<in> {R'. \<forall>i. \<acute>R i = Some True \<longrightarrow> R' i = Some True};;
        svc\<^sub>aRequest;;
        \<langle>svc\<^sub>aEnable,, \<acute>ghostU := \<acute>ghostU (i := User)\<rangle>);;
        WHILE  \<acute>svc\<^sub>aReq 
        DO
          SKIP
        OD
      ELSE IF \<acute>userSyscall = Block
      THEN
        \<langle>\<acute>ghostU := \<acute>ghostU (i := Syscall),, svc\<^sub>aDisable\<rangle>;;
        \<acute>R := \<acute>R (i := Some False);;
        \<langle>\<acute>ghostU := \<acute>ghostU (i := Yield),, SVC_now\<rangle>;;
        \<acute>ghostU := \<acute>ghostU (i := Syscall);;
        \<langle>svc\<^sub>aEnable,, \<acute>ghostU := \<acute>ghostU (i := User)\<rangle>;;
        WHILE \<acute>svc\<^sub>aReq 
        DO
          SKIP
        OD
      FI FI"

definition
  eChronos_svc\<^sub>a_code
where
  "eChronos_svc\<^sub>a_code \<equiv>
      \<acute>ghostP := True;;
      (schedule;;
      context_switch True;;
      \<langle>\<acute>ghostP := False,, IRet\<rangle>)"

definition
  eChronos_svc\<^sub>s_code
where
  "eChronos_svc\<^sub>s_code \<equiv>
      \<acute>ghostS := True;;
      (schedule;;
      context_switch False;;
      \<langle>\<acute>ghostS := False,, IRet\<rangle>)"

definition
  eChronos_handler_code
where
  "eChronos_handler_code i \<equiv> \<acute>E :\<in> {E'. \<acute>E \<subseteq> E'};; svc\<^sub>aRequest;; \<langle>IRet\<rangle>"

definition
  eChronos_sys
where
  "eChronos_sys \<equiv> interleaving eChronos_init eChronos_app_code eChronos_handler_code
                                   eChronos_svc\<^sub>a_code eChronos_svc\<^sub>s_code"

lemmas eChronos_sys_defs =
                    eChronos_sys_def interleaving_def hardware_init_def
                    can_interrupt_def can_interrupt'_def
                    eChronos_init_def eChronos_app_code_def
                    eChronos_handler_code_def eChronos_svc\<^sub>a_code_def
                    eChronos_svc\<^sub>s_code_def control_def
                    svc\<^sub>aEnable_def svc\<^sub>aDisable_def ITake_def
                    IRet_def svc\<^sub>aTake_def svc\<^sub>aRequest_def
                    SVC_now_def schedule_def context_switch_def
thm eChronos_sys_def[simplified eChronos_sys_defs]

end