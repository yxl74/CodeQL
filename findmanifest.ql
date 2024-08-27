import java
import xml.XML

from XMLFile manifest, XMLElement component, string componentType, string componentName
where
  manifest.getBaseName() = "AndroidManifest.xml" and
  component.getFile() = manifest and
  component.getParent().getName() = "application" and
  componentType = component.getName() and
  componentType in ["activity", "service", "receiver", "provider"] and
  componentName = component.getAttributeValue("android:name")
select
  manifest.getAbsolutePath(),
  componentType,
  componentName,
  "Component found in AndroidManifest.xml"