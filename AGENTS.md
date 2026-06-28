# AGENTS.md

这是写给 Claude / 其他 coding agent / 后续维护者的约定。本仓库通过 GitHub Pages 从 `master` 分支发布，所以**仓库里的所有文件都会被公开**。在动手之前请先读完本文件。

## 站点结构

```
index.html                                  # 首页 portal
summer-school.html                          # 暑期学校 (两个平行班)
workshop.html                               # 数学智能研讨会
404.html

assets/styles.css                           # 全站唯一样式表

materials/
  summer-school/
    index.html                              # 暑校课件入口 (两班 landing)
    intro/index.html                        # 入门班 课件页
    advanced/index.html                     # 提高班 课件页
  workshop/
    index.html                              # 研讨会课件页
```

## 课程材料的访问路径 — 唯一入口规则

**学员/听众访问课程材料的唯一入口，是点击班级 / Workshop 卡片。**

- 暑校页 (`summer-school.html`) → 点击「入门班」卡片 → `materials/summer-school/intro/`
- 暑校页 (`summer-school.html`) → 点击「提高班」卡片 → `materials/summer-school/advanced/`
- 研讨会页 (`workshop.html`) → 底部 Materials CTA → `materials/workshop/`

**禁止**：
- 不要在首页 / 暑校页 / 研讨会页直接列出材料文件链接
- 不要在 `materials/summer-school/index.html` 之外再做一个"所有课件总览"页面
- 不要把任何一个班级的材料链接放到对方班级的页面上

班级 → 课件页 → 该班的全部讲义 / 代码，这是必经路径，且**两个班的材料完全独立分页**。

## 添加课程材料

把**编译产物**放进对应班级 / Workshop 的目录：

```
materials/summer-school/intro/lec-01-types.pdf
materials/summer-school/intro/lec-02-tactics.pdf
materials/summer-school/intro/code-week1.zip
materials/summer-school/advanced/lec-01-macros.pdf
materials/workshop/dong-bin-slides.pdf
```

然后在对应的 `index.html` 的「课程材料」section 加上链接。命名建议：`lec-NN-<topic>.pdf` / `<speaker>-<topic>.pdf`。

## 源文件（.tex / .lean / .aux / .log 等）—— **不要暴露**

GitHub Pages 服务整个仓库目录，`.gitignore` 不影响发布。所以**绝对不要**把以下文件提交到 `materials/` 树下：

- `.tex` / `.bib` / `.cls` / `.sty`（LaTeX 源）
- `.aux` / `.log` / `.out` / `.toc` / `.synctex.gz`（LaTeX 中间产物）
- `.lean` 单独的源文件（一份 `lean-project.zip` 是可以的）
- 任何讲师不希望被搜索引擎抓取 / 学生直接拿走源码的内容

正确做法：
1. **首选**：源文件留在讲师自己的 repo，本仓库只放编译好的 PDF。
2. 实在需要在本仓库放源：放到 `_sources/`（前缀下划线，**不要从任何 HTML 链接它**），并在 PR 描述里说明只供讲师协作。
3. 提供"源码下载"时：先打包成单个 `code.zip` / `lean-project.zip`，只链接这个压缩包，不要把展开后的目录摊开放在公开路径下。

## 班级内容

| 班级 | 主题 | 老师 |
|---|---|---|
| 入门班 | 类型论与 Lean4 入门 | 王铎磊、颜富彬、李一哲 |
| 提高班 | Lean4 的元编程 | 董安杰、王语同、徐天一 |

具体每周大纲、讲义列表，都加在对应班级页面 `materials/summer-school/{intro,advanced}/index.html` 的「课程材料」section 里，不要在 `summer-school.html` 上展开。

## 视觉 / 写作约定

- 中文为主，英文 eyebrow 标签 (`Materials · 课件` 这种)
- 标题用 Source Han Serif，等宽用 SF Mono / JetBrains Mono
- 卡片样式 `.track` / `.track--alt` 都是可点击 `<a>`，带 `查看课件 →` CTA；不要做装饰性、不可点的卡片
- 不要用 emoji（除非用户明确要求）
- 不要新增 README.md / 文档文件（除本 AGENTS.md 外）—— 写说明请直接更新本页
