# buptLab-parser

这个仓库包含了北京邮电大学 2024-2025 秋季学期《编译原理与技术》课程实验——语法分析程序的相关代码和报告（见 Release）。

## 实验内容

1. 使用 Yacc 构建后缀表达式语法分析器；
2. 使用 JavaCC 构建算数表达式语法分析器；
3. 使用 C++ 实现 LL(1) 预测分析表自动生成算法和 LL(1) 语法分析程序；
4. 使用 C++ 实现 LR(1) 分析表自动生成算法和 LR(1) 语法分析程序。

## 快速开始

将当前目录切换到您想要测试的实验任务目录（如 `task1-yacc`），在该目录下执行 `make test` 命令，这将编译源代码（如果需要）并运行测试。

## 目录结构

```
.
├── LICENSE
├── README.md
└── task<n>-<technique>
    ├── Makefile         # 构建脚本
    ├── src              # 源代码目录
    │   └── main.<lang>  # 主程序文件，<lang> 是指使用的编程语言，如 yacc, cpp 等
    └── test             # 测试目录
        ├── testdata<n>.ans  # 测试答案文件
        └── testdata<n>.in   # 测试输入文件
```
