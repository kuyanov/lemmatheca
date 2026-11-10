from django import template

register = template.Library()


@register.filter
def compact_count(value):
    """Shorten counts from 1,000, with one decimal only below ten units."""
    if value is None:
        return "—"
    count = int(value)
    magnitude = abs(count)
    if magnitude < 1000:
        return str(count)

    suffixes = "kmbt"
    unit, scale = 0, 1000
    while magnitude >= scale * 1000 and unit < len(suffixes) - 1:
        unit, scale = unit + 1, scale * 1000
    precision = 10 if magnitude < scale * 10 else 1
    rounded = (magnitude * precision + scale // 2) // scale
    if rounded >= 1000 * precision and unit < len(suffixes) - 1:
        unit, scale, precision = unit + 1, scale * 1000, 10
        rounded = (magnitude * precision + scale // 2) // scale
    whole, fraction = divmod(rounded, precision)
    decimal = f".{fraction}" if fraction else ""
    sign = "-" if count < 0 else ""
    return f"{sign}{whole}{decimal}{suffixes[unit]}"
