; ModuleID = '.\LLcode\WhileIf.ll'
source_filename = ".\5CLLcode\5CWhileIF.cpp"
target datalayout = "e-m:w-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-windows-msvc19.16.27043"

; Function Attrs: noinline norecurse nounwind uwtable
define i32 @main() #0 !dbg !8 {
entry:
  br label %while.cond, !dbg !10

while.cond:                                       ; preds = %if.end, %entry
  %x.0 = phi i32 [ 0, %entry ], [ %x.1, %if.end ]
  %y.0 = phi i32 [ 0, %entry ], [ 7, %if.end ]
  %cmp = icmp slt i32 %x.0, 3, !dbg !11 
  br i1 %cmp, label %while.body, label %while.end, !dbg !10

while.body:                                       ; preds = %while.cond
  %add = add nsw i32 %x.0, 1, !dbg !12
  %add1 = add nsw i32 %y.0, 1, !dbg !13
  %cmp2 = icmp slt i32 %add, 4, !dbg !14
  br i1 %cmp2, label %if.then, label %if.else, !dbg !15

if.then:                                          ; preds = %while.body
  %inc = add nsw i32 %add, 1, !dbg !16
  br label %if.end, !dbg !17

if.else:                                          ; preds = %while.body
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %x.1 = phi i32 [ %inc, %if.then ], [ %x.0, %if.else ]
  br label %while.cond, !dbg !10, !llvm.loop !18

while.end:                                        ; preds = %while.cond
  ret i32 0, !dbg !20
}

attributes #0 = { noinline norecurse nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5, !6}
!llvm.ident = !{!7}

!0 = distinct !DICompileUnit(language: DW_LANG_C_plus_plus, file: !1, producer: "clang version 6.0.0 (tags/RELEASE_600/final)", isOptimized: false, runtimeVersion: 0, emissionKind: LineTablesOnly, enums: !2)
!1 = !DIFile(filename: ".\5CLLcode\5CWhileIF.cpp", directory: "F:\5CLLVM6\5Cbuild\5CDebug")
!2 = !{}
!3 = !{i32 2, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 2}
!6 = !{i32 7, !"PIC Level", i32 2}
!7 = !{!"clang version 6.0.0 (tags/RELEASE_600/final)"}
!8 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 1, type: !9, isLocal: false, isDefinition: true, scopeLine: 2, flags: DIFlagPrototyped, isOptimized: false, unit: !0, retainedNodes: !2)
!9 = !DISubroutineType(types: !2)
!10 = !DILocation(line: 6, column: 3, scope: !8)
!11 = !DILocation(line: 6, column: 11, scope: !8)
!12 = !DILocation(line: 8, column: 11, scope: !8)
!13 = !DILocation(line: 9, column: 11, scope: !8)
!14 = !DILocation(line: 10, column: 11, scope: !8)
!15 = !DILocation(line: 10, column: 9, scope: !8)
!16 = !DILocation(line: 12, column: 8, scope: !8)
!17 = !DILocation(line: 13, column: 5, scope: !8)
!18 = distinct !{!18, !10, !19}
!19 = !DILocation(line: 19, column: 3, scope: !8)
!20 = !DILocation(line: 20, column: 1, scope: !8)
