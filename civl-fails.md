# 2pc.bpl

## /noWitnessInference

```
CommutativityChecker_atomic_Coordinator_VoteYes_9_atomic_Coordinator_VoteYes_9
CommutativityChecker_atomic_Coordinator_VoteNo_9_atomic_Coordinator_VoteNo_9
CommutativityChecker_atomic_Participant_VoteReq_10_atomic_Participant_VoteReq_10
```

# verified-ft.bpl

## /noWitnessInference

```
Fork_20
Release_20
```

## /noCommutativityTriggers

```
CommutativityChecker_AtomicVC.Inc_11_AtomicVC.Copy_11
CommutativityChecker_AtomicVC.Inc_11_AtomicVC.Join_11
CommutativityChecker_AtomicVCSetElem_11_AtomicVC.Copy_11
CommutativityChecker_AtomicVCSetElem_11_AtomicVC.Join_11

CommutativityChecker_AtomicVC.Inc_20_AtomicVC.Copy_20
CommutativityChecker_AtomicVC.Inc_20_AtomicVC.Join_20
CommutativityChecker_AtomicVCSetElem_20_AtomicVC.Copy_20
CommutativityChecker_AtomicVCSetElem_20_AtomicVC.Join_20
```

# GC.bpl

| Z3 version | Time   | Notes |
| ---------- | ------:| ----- |
| z3-4.5.0   |  1 min |       |
| z3-4.6.0   | 22 min |       |
| z3-4.7.1   | 23 min |       |
| z3-4.8.1   |  crash |       |
| z3-4.8.3   |  crash |       |
| z3-4.8.4   |  3 min | 5 failed non-interference checks |
| z3-4.8.5   |  3 min | 5 failed non-interference checks |
