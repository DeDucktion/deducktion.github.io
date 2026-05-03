(() => {
	const t = document.createElement("link").relList;
	if (t && t.supports && t.supports("modulepreload")) return;
	for (const l of document.querySelectorAll('link[rel="modulepreload"]')) r(l);
	new MutationObserver((l) => {
		for (const o of l)
			if (o.type === "childList")
				for (const c of o.addedNodes)
					c.tagName === "LINK" && c.rel === "modulepreload" && r(c);
	}).observe(document, { childList: true, subtree: true });
	function n(l) {
		const o = {};
		return (
			l.integrity && (o.integrity = l.integrity),
			l.referrerPolicy && (o.referrerPolicy = l.referrerPolicy),
			l.crossOrigin === "use-credentials"
				? (o.credentials = "include")
				: l.crossOrigin === "anonymous"
					? (o.credentials = "omit")
					: (o.credentials = "same-origin"),
			o
		);
	}
	function r(l) {
		if (l.ep) return;
		l.ep = true;
		const o = n(l);
		fetch(l.href, o);
	}
})();
let N = 1,
	T = 0,
	A = 0;
function k(e, t, n) {
	(N = e), (T = t), (A = n), W();
}
function b() {
	return { scale: N, offsetX: T, offsetY: A };
}
function W() {
	const e = document.getElementById("transformLayer");
	e.style.transform = `translate(${T}px, ${A}px) scale(${N})`;
}
function j() {
	requestAnimationFrame(() => {
		const e = document.getElementById("canvas"),
			t = document.getElementById("proofViewport"),
			n = e.scrollWidth,
			r = e.scrollHeight;
		if (n === 0 || r === 0) return;
		const l = t.clientWidth,
			o = t.clientHeight,
			c = 40,
			{ scale: s, offsetX: i, offsetY: d } = b(),
			f = Math.min((l - c) / n, (o - c) / r, 1);
		f < s && k(f, i, d);
	});
}
function M() {
	const e = document.getElementById("canvas"),
		t = document.getElementById("proofViewport"),
		{ width: n, height: r } = e.getBoundingClientRect(),
		l = t.clientWidth,
		o = t.clientHeight;
	k(1, (l - n) / 2, (o - r) / 4);
}
class z {
	constructor() {
		(this.root = null), (this.selectedNode = null), (this.history = []);
	}
	createNode(t, n) {
		return {
			rule: t,
			premises: Array.from({ length: n }, () => this.emptyNode()),
			conclusion: null,
		};
	}
	emptyNode() {
		return { rule: null, premises: [], conclusion: null };
	}
	setSelected(t) {
		this.selectedNode = t;
	}
	pushHistory() {
		this.root &&
			this.history.push({ tree: structuredClone(this.root), transform: b() });
	}
	undo() {
		const t = this.history.pop();
		t &&
			((this.root = t.tree),
			k(t.transform.scale, t.transform.offsetX, t.transform.offsetY));
	}
}
function U(e) {
	const n = [
			"\u2192",
			"\xAC",
			"\u2227",
			"\u2228",
			"\\(",
			"\\)",
			"(?:A|E)",
			"[BCDEFGHIJKLMNOPQRSTUVWXYZ](?:_\\d+)?(?:\\^\\d+)?(?:[xyz](?:_\\d+)?)+",
			"[BCDEFGHIJKLMNOPQRSTUVWXYZ](?:_\\d+)?(?:\\^\\d+)?",
			"[xyz](?:_\\d+)?",
			"\\s+",
		].join("|"),
		r = new RegExp(n, "g"),
		l = [];
	let o;
	for (; (o = r.exec(e)) !== null; ) {
		const i = o[0];
		i.match(/^\s+$/) || l.push(i);
	}
	const c = l.join(""),
		s = e.replace(/\s+/g, "");
	return c !== s ? null : l;
}
function g(e) {
	const t = U(e);
	if (!t) return null;
	const n = V(t);
	if (n && n.rest.length === 0) return n.formula;
	if (t[0] === "\xAC") {
		const r = g(t.slice(1).join(""));
		return r ? { kind: "not", sub: r } : null;
	}
	if ((t[0] === "A" || t[0] === "E") && t[1]) {
		const r = g(t.slice(2).join(""));
		return r
			? t[0] === "A"
				? { kind: "forall", v: t[1], body: r }
				: { kind: "exists", v: t[1], body: r }
			: null;
	}
	if (t[0] === "(" && t[t.length - 1] === ")") {
		let r = 0;
		for (let l = 1; l < t.length; l++) {
			const o = t[l];
			if (
				(o === "(" && r++,
				o === ")" && r--,
				r === 0 && ["\u2227", "\u2228", "\u2192"].includes(o))
			) {
				const c = g(t.slice(1, l).join("")),
					s = g(t.slice(l + 1, -1).join(""));
				return !c || !s
					? null
					: o === "\u2227"
						? { kind: "and", left: c, right: s }
						: o === "\u2228"
							? { kind: "or", left: c, right: s }
							: { kind: "cond", left: c, right: s };
			}
		}
	}
	return null;
}
function V(e) {
	const t = /^([A-Z])(_\d+)?(\^(\d+))?/,
		n = /^[xyz](?:_\d+)?$/,
		r = t.exec(e[0]);
	if (!r) return null;
	const l = r[0],
		o = r[4] ? parseInt(r[4]) : 0,
		c = [];
	let s = 1;
	for (let i = 0; i < o; i++) {
		if (!e[s] || !n.test(e[s])) return null;
		c.push({ kind: "var", name: e[s] }), s++;
	}
	return e[s] && n.test(e[s])
		? null
		: { formula: { kind: "atom", pred: l, args: c }, rest: e.slice(s) };
}
function m(e) {
	switch (e.kind) {
		case "atom":
			return e.pred + e.args.map((t) => t.name).join("");
		case "not":
			return "\xAC" + m(e.sub);
		case "and":
			return `(${m(e.left)}\u2227${m(e.right)})`;
		case "or":
			return `(${m(e.left)}\u2228${m(e.right)})`;
		case "cond":
			return `(${m(e.left)}\u2192${m(e.right)})`;
		case "forall":
			return `A${e.v}${m(e.body)}`;
		case "exists":
			return `E${e.v}${m(e.body)}`;
	}
}
function u(e, t) {
	if (e.kind !== t.kind) return false;
	switch (e.kind) {
		case "atom":
			return (
				t.kind === "atom" &&
				e.pred === t.pred &&
				e.args.length === t.args.length &&
				e.args.every((n, r) => n.name === t.args[r].name)
			);
		case "not":
			return t.kind === "not" && u(e.sub, t.sub);
		case "and":
			return t.kind === "and" && u(e.left, t.left) && u(e.right, t.right);
		case "or":
			return t.kind === "or" && u(e.left, t.left) && u(e.right, t.right);
		case "cond":
			return t.kind === "cond" && u(e.left, t.left) && u(e.right, t.right);
	}
	return false;
}
const S = [
		{
			name: "and-intro",
			arity: 2,
			label: "\u2227I",
			latexlabel: "\\land I",
			typstlabel: "and I",
			check: (e, t) => {
				const [n, r] = e;
				return t.kind === "and" && u(t.left, n) && u(t.right, r);
			},
		},
		{
			name: "and-eli1",
			arity: 1,
			label: "\u2227E1",
			latexlabel: "\\land E1",
			typstlabel: "and E 1",
			check: (e, t) => {
				const [n] = e;
				return n.kind === "and" && u(n.left, t);
			},
		},
		{
			name: "and-eli2",
			arity: 1,
			label: "\u2227E2",
			latexlabel: "\\land E2",
			typstlabel: "and E 2",
			check: (e, t) => {
				const [n] = e;
				return n.kind === "and" && u(n.right, t);
			},
		},
		{
			name: "or-intro1",
			arity: 1,
			label: "\u2228I1",
			latexlabel: "\\lor I1",
			typstlabel: "or I 1",
			check: (e, t) => {
				const [n] = e;
				return t.kind === "or" && u(t.left, n);
			},
		},
		{
			name: "or-intro2",
			arity: 1,
			label: "\u2228I2",
			latexlabel: "\\lor I2",
			typstlabel: "or I 2",
			check: (e, t) => {
				const [n] = e;
				return t.kind === "or" && u(t.right, n);
			},
		},
		{
			name: "or-eli",
			arity: 3,
			label: "\u2228E",
			latexlabel: "\\lor E",
			typstlabel: "or E",
			check: (e, t) => {
				const [n, r, l] = e;
				return n.kind === "or" && u(r, t) && u(l, t);
			},
		},
		{
			name: "cond-intro",
			arity: 1,
			label: "\u2192I",
			latexlabel: "\\to I",
			typstlabel: "-> I",
			check: (e, t) => {
				const [n] = e;
				return t.kind === "cond" && u(t.right, n);
			},
		},
		{
			name: "cond-eli",
			arity: 2,
			label: "\u2192E",
			latexlabel: "\\to E",
			typstlabel: "-> E",
			check: (e, t) => {
				const [n, r] = e;
				return n.kind === "cond" && u(n.left, r) && u(n.right, t);
			},
		},
		{
			name: "neg-intro",
			arity: 2,
			label: "\xACI",
			latexlabel: "\\lnot I",
			typstlabel: "not I",
			check: (e, t) => {
				const [n, r] = e;
				return (
					t.kind === "not" &&
					((n.kind === "not" && u(n.sub, r)) ||
						(r.kind === "not" && u(r.sub, n)))
				);
			},
		},
		{
			name: "neg-eli",
			arity: 2,
			label: "\xACE",
			latexlabel: "\\lnot E",
			typstlabel: "not E",
			check: (e, t) => {
				const [n, r] = e;
				return (
					(n.kind === "not" && u(n.sub, r)) || (r.kind === "not" && u(r.sub, n))
				);
			},
		},
	],
	_ = new Map(S.map((e) => [e.name, e]));
function v(e) {
	return _.get(e);
}
function Y(e) {
	if (!e.rule || !e.conclusion) return null;
	const t = e.rule ? v(e.rule) : void 0;
	if (!t) return null;
	if (e.premises.length !== t.arity) return false;
	const n = e.premises.map((r) => r.conclusion);
	return n.some((r) => r == null) ? null : t.check(n, e.conclusion);
}
function E(e, t) {
	var _a;
	if (!e.rule) return e.conclusion ? t.some((r) => u(r, e.conclusion)) : null;
	if (!e.conclusion) return null;
	let n = t;
	if (e.rule === "cond-intro") {
		if (e.conclusion.kind !== "cond") return false;
		n = [...t, e.conclusion.left];
	}
	if (e.rule === "neg-intro") {
		if (e.conclusion.kind !== "not") return false;
		n = [...t, e.conclusion.sub];
	}
	if (e.rule === "neg-eli") {
		if (!e.conclusion) return null;
		n = [...t, { kind: "not", sub: e.conclusion }];
	}
	if (e.rule === "or-eli") {
		if (e.premises.length !== 3) return false;
		const r = (_a = e.premises[0]) == null ? void 0 : _a.conclusion;
		if (!r || r.kind !== "or") return false;
		const l = [...t, r.left],
			o = [...t, r.right],
			c = E(e.premises[0], t);
		if (c !== true) return c;
		const s = E(e.premises[1], l);
		if (s !== true) return s;
		const i = E(e.premises[2], o);
		return i !== true ? i : Y(e);
	}
	for (const r of e.premises) {
		const l = E(r, n);
		if (l !== true) return l;
	}
	return Y(e);
}
function D(e) {
	if (e.trim() === "") return [];
	const t = e.split(","),
		n = [];
	for (const r of t) {
		const l = g(r.trim());
		if (!l) return null;
		n.push(l);
	}
	return n;
}
function K(e) {
	return g(e.trim());
}
function Z(e, t, n) {
	if (!e) return null;
	const r = D(t);
	if (!r) return null;
	const l = K(n);
	if (!l) return null;
	const o = E(e, r);
	return o !== true ? o : e.conclusion ? !!u(e.conclusion, l) : null;
}
function G(e) {
	e.innerHTML = "";
	for (const t of S) {
		const n = document.createElement("button");
		(n.textContent = t.label),
			(n.onclick = () => {
				a.pushHistory();
				const r = a.createNode(t.name, t.arity);
				a.selectedNode
					? Object.assign(a.selectedNode, r)
					: ((a.root = r), (a.selectedNode = r)),
					I(document.getElementById("canvas"));
			}),
			e.appendChild(n);
	}
}
function $(e) {
	let t = "";
	const n = {
			"<": "\u2227",
			and: "\u2227",
			"&": "\u2227",
			">": "\u2228",
			or: "\u2228",
			"|": "\u2228",
			"~": "\xAC",
			not: "\xAC",
			"->": "\u2192",
			to: "\u2192",
		},
		r = Math.max(...Object.keys(n).map((l) => l.length));
	e.addEventListener("input", () => {
		const l = e.selectionStart ?? 0,
			o = e.selectionEnd ?? 0;
		t = e.value.slice(Math.max(0, l - r), l);
		const c = Object.keys(n).sort((s, i) => i.length - s.length);
		for (const s of c)
			if (t.endsWith(s)) {
				const i = n[s],
					d = e.value;
				(e.value = d.slice(0, l - s.length) + i + d.slice(o)),
					(e.selectionStart = e.selectionEnd = l - s.length + i.length),
					(t = "");
				break;
			}
	});
}
let X = false;
function I(e, t = true) {
	if (((e.innerHTML = ""), !a.root)) return;
	const n = R(a.root);
	e.appendChild(n),
		requestAnimationFrame(() => {
			q(), t && j(), X || (M(), (X = true));
		});
}
function R(e) {
	const t = document.createElement("div");
	t.className = "tree-node";
	const n = document.createElement("div");
	n.className = "premises";
	for (const s of e.premises) {
		const i = R(s),
			d = i.querySelector("input.conclusion-input");
		d && $(d), n.appendChild(i);
	}
	t.appendChild(n);
	const r = document.createElement("div");
	r.className = e.rule ? "rule-line" : "rule-line hidden";
	const l = document.createElement("div");
	l.className = "line";
	const o = document.createElement("span");
	(o.className = "rule-label"),
		e.rule &&
			(console.log(S),
			(o.textContent = v(e.rule) ? v(e.rule).label : e.rule),
			r.appendChild(l),
			r.appendChild(o)),
		t.appendChild(r);
	const c = document.createElement("input");
	return (
		(c.className = "conclusion-input"),
		(c.value = e.conclusion ? m(e.conclusion) : ""),
		(c.oninput = () => {
			const s = g(c.value);
			e.conclusion = s;
		}),
		$(c),
		t.appendChild(c),
		(t.onclick = (s) => {
			s.stopPropagation(), a.setSelected(e);
		}),
		t
	);
}
function q() {
	const e = Array.from(document.querySelectorAll(".tree-node"));
	for (const t of e) {
		const n = Array.from(t.querySelectorAll(":scope > .premises > .tree-node"));
		if (n.length === 0) continue;
		const r = [];
		for (const f of n) {
			const p = f.querySelector(":scope > input.conclusion-input");
			p && r.push(p);
		}
		if (r.length === 0) continue;
		let l = 1 / 0,
			o = -1 / 0;
		for (const f of r) {
			const p = f.offsetLeft,
				x = f.offsetLeft + f.offsetWidth;
			(l = Math.min(l, p)), (o = Math.max(o, x));
		}
		const c = o - l,
			s = t.querySelector(":scope > .rule-line > .line");
		s &&
			((s.style.position = "absolute"),
			(s.style.left = `${l}px`),
			(s.style.width = `${c}px`));
		const i = t.querySelector(":scope > .rule-line > .rule-label");
		i && ((i.style.position = "absolute"), (i.style.left = `${l + c + 1}px`));
		const d = t.querySelector(":scope > .conclusion-input");
		if (d) {
			const f = d.offsetLeft + d.offsetWidth / 2,
				p = l + c / 2;
			(d.style.position = "relative"), (d.style.left = `${p - f}px`);
		}
	}
}
function h(e) {
	switch (e.kind) {
		case "atom":
			return e.pred;
		case "not":
			return `not ${h(e.sub)}`;
		case "and":
			return `(${h(e.left)} and ${h(e.right)})`;
		case "or":
			return `(${h(e.left)} or ${h(e.right)})`;
		case "cond":
			return `(${h(e.left)} -> ${h(e.right)})`;
	}
	return "";
}
function O(e) {
	if (!e.conclusion)
		throw new Error("Node without conclusion cannot be exported");
	const t = `$${h(e.conclusion)}$`;
	if (!e.rule) return t;
	const n = v(e.rule);
	if (!n) throw new Error(`Unknown rule: ${e.rule}`);
	const r = e.premises.map((l) => O(l));
	return `rule(
    name: $${n.typstlabel}$,
    ${r.join(`,
`)},
    ${t}
    )`;
}
function J(e) {
	return `#prooftree(
    ${O(e)}
    )`;
}
function y(e) {
	switch (e.kind) {
		case "atom":
			return e.pred;
		case "not":
			return `\\lnot ${y(e.sub)}`;
		case "and":
			return `(${y(e.left)} \\land ${y(e.right)})`;
		case "or":
			return `(${y(e.left)} \\lor ${y(e.right)})`;
		case "cond":
			return `(${y(e.left)} \\to ${y(e.right)})`;
	}
	return "";
}
function Q(e) {
	switch (e) {
		case 0:
			return "";
		case 1:
			return "\\UnaryInfC";
		case 2:
			return "\\BinaryInfC";
		case 3:
			return "\\TrinaryInfC";
		default:
			throw new Error(`Unsupported arity: ${e}`);
	}
}
function P(e) {
	if (!e.conclusion)
		throw new Error("Node without conclusion cannot be exported");
	const t = `$${y(e.conclusion)}$`;
	if (!e.rule) return `\\AxiomC{${t}}`;
	const n = v(e.rule);
	if (!n) throw new Error("Unknown rule");
	const r = [];
	for (const l of e.premises) r.push(P(l));
	return (
		r.push(`\\RightLabel{$${n.latexlabel}$}`),
		r.push(`${Q(n.arity)}{${t}}`),
		r.join(`
`)
	);
}
function ee(e) {
	return `
    \\begin{prooftree}
    ${P(e)}
    \\end{prooftree}
    `.trim();
}
const a = new z(),
	te = document.getElementById("transformLayer");
let ne = 1,
	re = 0,
	oe = 0,
	B = false,
	L = 0,
	C = 0;
function le() {
	te.style.transform = `translate(${re}px, ${oe}px) scale(${ne})`;
}
window.addEventListener("DOMContentLoaded", () => {
	G(document.getElementById("rules"));
	const e = document.getElementById("premises"),
		t = document.getElementById("conclusion");
	$(e),
		$(t),
		(a.root = null),
		(a.selectedNode = null),
		I(document.getElementById("canvas")),
		le(),
		I(document.getElementById("canvas")),
		window.addEventListener("resize", () => {
			requestAnimationFrame(() => {
				q(), j();
			});
		}),
		(document.getElementById("undoBtn").onclick = () => {
			a.undo(), I(document.getElementById("canvas"), false);
		}),
		(document.getElementById("validateBtn").onclick = () => {
			const o = document.getElementById("premises"),
				c = document.getElementById("conclusion"),
				s = document.getElementById("result");
			console.log(o.value, c.value);
			const i = Z(a.root, o.value, c.value);
			console.log("deductionnode:", a.root),
				s &&
					(i === true
						? (s.textContent = "Correct proof")
						: i === false
							? (s.textContent = "Incorrect proof")
							: (s.textContent = "Syntax Error"));
		}),
		(document.getElementById("practiceBtn").onclick = () => {}),
		(document.getElementById("clearTreeBtn").onclick = () => {
			(a.root = null),
				(a.selectedNode = null),
				(a.history = []),
				I(document.getElementById("canvas")),
				M();
		}),
		(document.getElementById("clearInputBtn").onclick = () => {
			const o = document.getElementById("premises"),
				c = document.getElementById("conclusion"),
				s = document.getElementById("result");
			(o.value = ""),
				(c.value = ""),
				s && (s.textContent = "No validation yet");
		}),
		(document.getElementById("convertTypBtn").onclick = async () => {
			if (!a.root) {
				alert("No prooftree to export");
				return;
			}
			try {
				const o = J(a.root);
				await navigator.clipboard.writeText(o),
					alert("Typst code copied to clipboard");
			} catch (o) {
				console.error(o), alert("Export faild");
			}
		}),
		(document.getElementById("convertTexBtn").onclick = async () => {
			if (!a.root) {
				alert("No prooftree to export");
				return;
			}
			try {
				const o = ee(a.root);
				await navigator.clipboard.writeText(o),
					alert("Latex code copied to clipboard");
			} catch (o) {
				console.error(o), alert("Export faild");
			}
		});
	const n = document.getElementById("proofViewport");
	n.addEventListener(
		"wheel",
		(o) => {
			o.preventDefault();
			const c = n.getBoundingClientRect(),
				s = o.clientX - c.left,
				i = o.clientY - c.top,
				{ scale: d, offsetX: f, offsetY: p } = b(),
				x = o.deltaY < 0 ? 1.1 : 0.9,
				w = Math.min(3, Math.max(0.2, d * x)),
				H = s - ((s - f) / d) * w,
				F = i - ((i - p) / d) * w;
			k(w, H, F);
		},
		{ passive: false },
	),
		n.addEventListener("mousedown", (o) => {
			(B = true), (L = o.clientX), (C = o.clientY);
		}),
		window.addEventListener("mousemove", (o) => {
			if (!B) return;
			const { scale: c, offsetX: s, offsetY: i } = b();
			k(c, s + o.clientX - L, i + o.clientY - C),
				(L = o.clientX),
				(C = o.clientY);
		}),
		window.addEventListener("mouseup", () => (B = false));
	const r = document.getElementById("themeToggle");
	r.onclick = () => {
		const o = document.documentElement,
			c = o.dataset.theme === "light" ? "dark" : "light";
		(o.dataset.theme = c), localStorage.setItem("theme", c);
	};
	const l = localStorage.getItem("theme");
	l && (document.documentElement.dataset.theme = l);
});
