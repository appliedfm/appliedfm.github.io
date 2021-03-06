---
layout: splash
header:
  overlay_color: "#000"
  overlay_filter: "0.5"
  overlay_image: /assets/images/rooster-unsplash-ilona-frey.jpg
  actions:
    - label: "About Us"
      url: "/about/"
  caption: "Photo by [Ilona Frey](https://unsplash.com/@couleuroriginal) on Unsplash"
excerpt: "Supporting open source projects in the Coq ecosystem."

intro: 
  - excerpt: 'Mechanized logic is transforming computer science. We are working to help make it happen. [Find out more](/about/).'

feature_row:
  - image_path: /assets/images/rooster-unsplash-michael-anfang.jpg
    image_caption: "[Michael Anfang](https://unsplash.com/@manfang) on Unsplash"
    alt: "Image of a rooster"
    title: "Placeholder 1"
    excerpt: "This is some sample content that goes here with **Markdown** formatting."
  - image_path: /assets/images/rooster-unsplash-ram-kumar.jpg
    image_caption: "[Ram Kumar](https://unsplash.com/@ramkumar810) on Unsplash"
    alt: "Image of a rooster"
    title: "Placeholder 2"
    excerpt: "This is some sample content that goes here with **Markdown** formatting."
    url: "/about/"
    btn_label: "Read More"
    btn_class: "btn--primary"
  - image_path: /assets/images/rooster-unsplash-chuttersnap.jpg
    image_caption: "[CHUTTERSNAP](https://unsplash.com/@chuttersnap) on Unsplash"
    title: "Placeholder 3"
    excerpt: "This is some sample content that goes here with **Markdown** formatting."

feature_row2:
  - image_path: /assets/images/rooster-unsplash-ben-hummitzsch.jpg
    image_caption: "[Ben Hummitzsch](https://unsplash.com/@benhumee) on Unsplash"
    alt: "Image of a rooster"
    title: "FM Growth"
    excerpt: 'We are measuring the growth of formal methods in open source communities.'
    url: "https://growth.applied.fm"
    btn_label: "Read the Report"
    btn_class: "btn--primary"

feature_row3:
  - image_path: /assets/images/rooster-unsplash-fabian-joy.jpg
    image_caption: "[Fabian Joy](https://unsplash.com/@fab_joy) on Unsplash"
    alt: "Image of a rooster"
    title: "vstyle: a style guide for Coq"
    excerpt: 'Style is a highly visible property of open source software. It impacts most of the workflows involving source code. *Good* style improves productivity by accounting for those workflows. To bring the benefits of good style to the masses, we are working with the community to identify & document the best practices for open source projects in the Coq ecosystem.'
    url: "https://vstyle.readthedocs.io"
    btn_label: "Learn More"
    btn_class: "btn--primary"

feature_row4:
  - image_path: /assets/images/rooster-unsplash-rd-smith.jpg
    image_caption: "[R.D. Smith](https://unsplash.com/@rd421) on Unsplash"
    alt: "Image of a rooster"
    title: "Placeholder Image Center Aligned"
    excerpt: 'This is some sample content that goes here with **Markdown** formatting. Centered with `type="center"`'
    url: "#test-link"
    btn_label: "Read More"
    btn_class: "btn--primary"
---

{% include feature_row id="intro" type="center" %}

<!-- {% include feature_row %} -->

{% include feature_row id="feature_row2" type="left" %}

{% include feature_row id="feature_row3" type="right" %}

<!-- {% include feature_row id="feature_row4" type="center" %} -->


<!--
# Recent posts

{% assign entries_layout = page.entries_layout | default: 'list' %}
<div class="entries-{{ entries_layout }}">
  {% for post in site.posts limit:3 %}
    {% include archive-single.html type=entries_layout %}
  {% endfor %}
</div>
-->