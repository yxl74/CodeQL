import java
import codeql.xml.Xml

from File manifest, XmlElement component, string componentName
where
  manifest.getBaseName() = "AndroidManifest.xml" and
  component.getFile() = manifest and
  component.getName() in ["activity", "service", "receiver", "provider"] and
  componentName = component.getAttributeValue("android:name")
select
  manifest.getAbsolutePath() as ManifestPath,
  component.getName() as ComponentType,
  componentName as ComponentName