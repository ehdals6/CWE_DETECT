BAP설치는 해당 링크에서 다운가능합니다.
(https://github.com/BinaryAnalysisPlatform/bap)
현재 코드에서 진행한 버전은 BAP 2.1.0버전입니다.

설치: 해당 폴더에서 makefile을 사용하여 설치합니다. (동작은 bap-toolkit과 동일)
(https://github.com/BinaryAnalysisPlatform/bap-toolkit)

1) make
2) make install

일반 패턴 탐지
1) 테스트를 진행할 경로로 이동한다. (예 $cd sample)
2) bap [실행파일] --[탐지모듈]-fun_name=[함수명] --pass=[탐지모듈]
  --> 예: $bap test125_mac --CWE125-fun_name=_main --pass=CWE125

패턴 탐지 모듈 리스트: CWE125, CWE190, CWE416, CWE476, CWE787

Primus 에뮬레이터 탐지
1) 테스트를 진행할 경로로 이동한다. (예 $cd sample)
2) bap [실행파일] --recipe=[탐지모듈]:entry-points=[함수명]
  --> 예: $bap test125 --recipe=CWE125:entry-points=main
3) 실행 후 해당폴더의 incident파일을 확인한다.

에뮬레이터 탐지 모듈 리스트: CWE125, CWE190, CWE415, CWE787

*주의사항 일반 샘플과 다르게 커널시험시 메모리의 크기가 64GB이상 권장드립니다.
에뮬레이터의 경우 메모리공간이 더욱 필요합니다.
