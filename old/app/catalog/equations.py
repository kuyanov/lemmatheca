"""Resolve entry-local LaTeX equation labels before handing formulas to KaTeX."""

import re

from .sources import ContentError, Element

LABEL = re.compile(r'\\label\{([A-Za-z0-9][A-Za-z0-9_.:-]*)\}')
EQREF = re.compile(r'\\eqref\{([^{}]+)\}')
MATH = re.compile(r'(\\\[.*?\\\]|\\\(.*?\\\))', re.DOTALL)


def prepare_equations(root):
    numbers = {}
    for node in root.walk():
        if node.tag not in ('div', 'p') or 'math-display' not in node.attrs.get('class', '').split():
            continue
        text = node.text()
        labels = LABEL.findall(text)
        if not labels:
            continue
        match = re.fullmatch(r'\s*\\\[(.*?)\\\]\s*', text, re.DOTALL)
        if len(labels) != 1 or not match or any(isinstance(child, Element) for child in node.children):
            raise ContentError(
                'Use one equation label in one plain display-math element')
        label = labels[0]
        if label in numbers or (node.attrs.get('id') and node.attrs['id'] != label):
            raise ContentError(
                f'Duplicate or conflicting equation label: {label}')
        if r'\tag' in text:
            raise ContentError(
                'Labelled equations are numbered automatically; omit \\tag')
        number = len(numbers) + 1
        numbers[label] = number
        node.attrs['id'] = label
        node.children = [
            r'\[' + LABEL.sub('', match[1]) + rf'\tag{{{number}}}\]']

    def number(label):
        if label not in numbers:
            raise ContentError(f'Unknown equation reference: {label}')
        return f'({numbers[label]})'

    def link(label):
        return Element('a', {'href': '#' + label, 'class': 'equation-reference',
                             'aria-label': 'Equation ' + str(numbers.get(label, ''))}, [number(label)])

    def expand(text):
        result = []
        for part in MATH.split(text):
            if part.startswith((r'\[', r'\(')):
                standalone = EQREF.fullmatch(
                    part[2:-2].strip()) if part.startswith(r'\(') else None
                if standalone:
                    result.append(link(standalone[1]))
                else:
                    result.append(
                        EQREF.sub(lambda match: r'\text{' + number(match[1]) + '}', part))
            else:
                position = 0
                for match in EQREF.finditer(part):
                    result.extend(
                        [part[position:match.start()], link(match[1])])
                    position = match.end()
                result.append(part[position:])
        return result

    def visit(node):
        if node.tag in ('pre', 'code', 'script', 'style'):
            return
        children = []
        for child in node.children:
            if isinstance(child, Element):
                visit(child)
                children.append(child)
            else:
                if r'\label{' in child:
                    raise ContentError(
                        'Equation labels belong inside a math-display element')
                children.extend(expand(child))
        node.children = children
    visit(root)
