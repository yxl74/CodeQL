import java
import codeql.xml.Xml

from File manifest, XmlElement component, string componentType, string componentName
where
  manifest.getBaseName() = "AndroidManifest.xml" and
  component.getFile() = manifest and
  componentType = component.getName() and
  componentType in ["activity", "service", "receiver", "provider", "application"] and
  (
    componentName = component.getAttributeValue("android:name")
    or
    componentName = component.getAttributeValue("name")
    or
    not exists(component.getAttributeValue("android:name")) and
    not exists(component.getAttributeValue("name")) and
    componentName = "No name attribute"
  )
select
  manifest.getAbsolutePath(),
  componentType,
  componentName,
  "Potential component found in AndroidManifest.xml"